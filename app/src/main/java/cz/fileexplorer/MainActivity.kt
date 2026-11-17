package cz.fileexplorer

import android.app.Activity
import android.app.AlertDialog
import android.content.Intent
import org.json.JSONArray
import org.json.JSONObject
import android.graphics.Canvas
import android.graphics.Paint
import android.graphics.Path
import android.graphics.RectF
import android.graphics.Color
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.text.Editable
import android.text.TextWatcher
import android.view.Gravity
import android.net.Uri
import android.os.Bundle
import android.os.Build
import android.os.Environment
import android.os.Handler
import android.os.Looper
import android.provider.Settings
import android.provider.MediaStore
import android.content.ContentUris
import android.graphics.Bitmap
import android.util.LruCache
import android.content.pm.PackageManager
import android.Manifest
import android.util.Size
import java.util.Date
import java.text.SimpleDateFormat
import java.util.Locale
import android.content.ActivityNotFoundException
import androidx.core.content.FileProvider
import android.webkit.MimeTypeMap
import android.provider.DocumentsContract
import android.view.ViewGroup
import android.view.View
import android.view.WindowInsets
import android.widget.*
import androidx.documentfile.provider.DocumentFile
import com.hierynomus.smbj.SMBClient
import com.hierynomus.smbj.auth.AuthenticationContext
import com.hierynomus.smbj.connection.Connection
import com.hierynomus.smbj.session.Session
import com.hierynomus.smbj.share.DiskShare
import com.hierynomus.msdtyp.AccessMask
import com.hierynomus.mssmb2.SMB2ShareAccess
import com.hierynomus.mssmb2.SMB2CreateDisposition
import com.hierynomus.mssmb2.SMB2CreateOptions
import java.io.File
import android.content.ContentValues
import android.graphics.BitmapFactory
import android.provider.OpenableColumns
import com.google.mlkit.vision.documentscanner.GmsDocumentScanning
import com.google.mlkit.vision.documentscanner.GmsDocumentScannerOptions
import com.google.mlkit.vision.documentscanner.GmsDocumentScanningResult
import java.util.concurrent.Executors
import java.util.zip.ZipEntry
import java.util.zip.ZipInputStream
import java.util.zip.ZipOutputStream
import android.widget.PopupWindow

class MainActivity : Activity() {
    // Set these to your own public donation destinations before publishing.
    private val donationPageUrl = "https://ko-fi.com/pruzkumnik"
    private val donationSolanaAddress = "C5LH6LDigi2DvhmqskCZ4fvp37panR6FPYVAbswwg4pc"
    private val io = Executors.newSingleThreadExecutor()
    private lateinit var root: LinearLayout
    private var localRoot: DocumentFile? = null
    private var local: DocumentFile? = null
    private var share: DiskShare? = null
    private var connection: Connection? = null
    private var session: Session? = null
    private var host = ""
    private var shareName = ""
    private var smbPath = ""
    // Credentials are held only for this Activity lifetime, never written to preferences.
    private var smbUser = ""
    private var smbPassword = CharArray(0)
    private var smbDomain = ""

    private fun closeSmbQuietly() {
        try { share?.close() } catch (_: Exception) {}
        try { session?.close() } catch (_: Exception) {}
        try { connection?.close() } catch (_: Exception) {}
        share = null; session = null; connection = null
    }

    private fun reconnectSmb(): DiskShare {
        // Avoid letting a failed LOGOFF prevent a new connection.
        closeSmbQuietly()
        val c = SMBClient().connect(host)
        try {
            val ss = c.authenticate(AuthenticationContext(smbUser, smbPassword, smbDomain))
            try {
                val sh = ss.connectShare(shareName) as DiskShare
                connection = c; session = ss; share = sh
                return sh
            } catch (e: Exception) {
                try { ss.close() } catch (_: Exception) {}
                throw e
            }
        } catch (e: Exception) {
            try { c.close() } catch (_: Exception) {}
            throw e
        }
    }

    // All SMB operations run on the single-thread executor. Retry once if the
    // server has closed the share/session between browsing and a file transfer.
    private fun <T> withSmb(block: (DiskShare) -> T): T {
        val current = share ?: reconnectSmb()
        return try { block(current) } catch (first: Exception) {
            val detail = generateSequence(first as Throwable?) { it.cause }
                .mapNotNull { it.message }.joinToString(" ").lowercase()
            val disconnected = detail.contains("already been closed") ||
                detail.contains("closed") || detail.contains("logoff") ||
                detail.contains("connection reset") || detail.contains("broken pipe")
            if (!disconnected) throw first
            block(reconnectSmb())
        }
    }
    private var mode = "home"
    private var phoneDir: File = Environment.getExternalStorageDirectory()
    private var pendingPhoneDir: File? = null
    private var awaitingPermission = false
    private val folderRequest = 11
    private val uploadRequest = 12
    private val saveRequest = 13
    private val scannerRequest = 215
    private val scanFolderRequest = 216
    private val scanCopyFolderRequest = 218
    private var pendingScanCopy: Pair<Uri, String>? = null
    private var scannedPages: List<Uri> = emptyList()
    private var scannedPdf: Uri? = null
    private var scanOutputFormat = "pdf"
    private val selectedScans = linkedSetOf<Uri>()
    private var scans = listOf<Pair<Uri, String>>()

    private val photoDeleteRequest = 214
    private var pendingPhotoDeletion: List<Uri> = emptyList()
    private var pendingDownload: String? = null
    private var pendingUploadPath = ""
    private var pendingUploadLocal = false
    private var selectedLocal: DocumentFile? = null
    private var selectedRemote: String? = null
    private val selectedFiles = linkedSetOf<File>()
    private var selectionMode = false
    private var clipboardFiles: List<File> = emptyList()
    private var clipboardMove = false
    private var transferBusy = false
    private data class RecentPhoto(val uri: Uri, val name: String, val timestamp: Long)
    private val selectedPhotos = linkedSetOf<Uri>()
    private var recentPhotos: List<RecentPhoto> = emptyList()
    private var photoScreen = "all"
    private var allPhotosSelectionMode = false
    private var mediaScreen = "video"
    private val selectedMedia = linkedSetOf<Uri>()
    private var mediaItems: List<RecentPhoto> = emptyList()
    private var photoScrollIndex = 0
    private val thumbCache = object : LruCache<String, Bitmap>(80) {}
    private val thumbnailPool = Executors.newFixedThreadPool(3)
    private fun photoLayout(): String = getSharedPreferences("explorer", MODE_PRIVATE)
        .getString("photo_layout", "large") ?: "large"
    private fun setPhotoLayout(layout: String) {
        getSharedPreferences("explorer", MODE_PRIVATE).edit().putString("photo_layout", layout).apply()
        showPhotoGallery(photoScreen)
    }

    private var photoClipboard: List<RecentPhoto> = emptyList()
    // Community: share through user-installed apps, never to a hardcoded recipient.
    private fun shareSelectedPhotos(packageName: String? = null) {
        val uris = ArrayList(recentPhotos.filter { it.uri in selectedPhotos }.map { it.uri })
        if (uris.isEmpty()) { message("Select photos first"); return }
        val intent = Intent(if (uris.size == 1) Intent.ACTION_SEND else Intent.ACTION_SEND_MULTIPLE).apply {
            type = "image/*"
            if (uris.size == 1) putExtra(Intent.EXTRA_STREAM, uris.first())
            else putParcelableArrayListExtra(Intent.EXTRA_STREAM, uris)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
            val clip = android.content.ClipData.newUri(contentResolver, "Photos", uris.first())
            uris.drop(1).forEach { clip.addItem(android.content.ClipData.Item(it)) }
            clipData = clip
            if (packageName != null) setPackage(packageName)
        }
        try { startActivity(if (packageName == null) Intent.createChooser(intent, "Share photos") else intent) }
        catch (_: Exception) { message("App not installed or cannot receive photos") }
    }

    private fun language(): String = getSharedPreferences("community", MODE_PRIVATE)
        .getString("language", "en") ?: "en"
    private fun translated(en: String, cs: String, de: String): String = when (language()) {
        "cs" -> cs
        "de" -> de
        "en" -> en
        else -> when (resources.configuration.locales[0].language) {
            "cs" -> cs
            "de" -> de
            else -> en
        }
    }
    private fun settingsSection(title: String) {
        root.addView(label(title, 12, accent, true).apply {
            letterSpacing = 0.12f
            setPadding(dp(8), dp(19), 0, dp(10))
        })
    }
    private fun settingsItem(icon: String, title: String, subtitle: String, click: () -> Unit) {
        val line = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
            background = shape(panel, 17); setPadding(dp(14), dp(12), dp(12), dp(12))
            setOnClickListener { click() }
        }
        line.addView(label(icon, 25, accent).apply { gravity = Gravity.CENTER }, LinearLayout.LayoutParams(dp(44), dp(48)))
        val copy = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(dp(9), 0, 0, 0) }
        copy.addView(label(title, 16, ink, true))
        copy.addView(label(subtitle, 12, muted))
        line.addView(copy, LinearLayout.LayoutParams(0, -2, 1f))
        line.addView(label("›", 27, muted), LinearLayout.LayoutParams(dp(20), -2))
        root.addView(line, LinearLayout.LayoutParams(-1, -2).apply { bottomMargin = dp(9) })
    }
    private fun scrollSettings(title: String, back: () -> Unit) {
        screen(title)
        val fixed = root
        val scroll = ScrollView(this).apply { clipToPadding = false }
        val content = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        scroll.addView(content)
        fixed.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1f))
        root = content
        settingsItem("‹", translated("Back", "Zpět", "Zurück"), "", back)
    }
    private fun openCommunitySettings() {
        scrollSettings(translated("Settings", "Nastavení", "Einstellungen")) { home() }
        settingsSection(translated("PERSONALIZATION", "PŘIZPŮSOBENÍ", "PERSONALISIERUNG"))
        settingsItem("🌐", translated("Language", "Jazyk", "Sprache"),
            when(language()) { "cs" -> "Čeština"; "de" -> "Deutsch"; "auto" -> translated("System default", "Podle telefonu", "Systemsprache"); else -> "English" }) { openLanguageSettings() }
        settingsItem("◐", translated("Appearance", "Vzhled", "Darstellung"),
            translated("Dark theme and display", "Tmavý motiv a zobrazení", "Dunkles Design und Anzeige")) { openAppearanceSettings() }
        settingsSection(translated("FILE MANAGEMENT", "SPRÁVA SOUBORŮ", "DATEIVERWALTUNG"))
        settingsItem("▦", translated("File browsing", "Procházení souborů", "Dateiansicht"),
            translated("Open storage and folders", "Úložiště a složky", "Speicher und Ordner")) { openFileSettings() }
        settingsItem("▰", translated("Storage", "Úložiště", "Speicher"),
            translated("Usage and available space", "Využití a volné místo", "Belegung und freier Platz")) { openStorageSettings() }
        settingsItem("⌁", translated("Network", "Síť", "Netzwerk"),
            translated("Windows shares (SMB)", "Sdílené složky Windows (SMB)", "Windows-Freigaben (SMB)")) { smbConnections() }
        settingsItem("▣", translated("ZIP manager", "Správce ZIP", "ZIP-Verwaltung"),
            translated("Create and extract archives", "Vytváření a rozbalování archivů", "Archive erstellen und entpacken")) { openZipManager() }
        settingsSection(translated("ABOUT & SUPPORT", "INFORMACE A PODPORA", "INFO & UNTERSTÜTZUNG"))
        settingsItem("♥", translated("Support development", "Podpořit vývoj", "Entwicklung unterstützen"),
            "Ko-fi  •  Solana (SOL)") { showDonate() }
        settingsItem("ⓘ", translated("About the app", "O aplikaci", "Über die App"),
            "File Explorer Community • 3.9") { openAboutSettings() }
    }
    private fun openLanguageSettings() {
        scrollSettings(translated("Language", "Jazyk", "Sprache")) { openCommunitySettings() }
        settingsSection(translated("SELECT LANGUAGE", "VÝBĚR JAZYKA", "SPRACHE WÄHLEN"))
        listOf("auto" to translated("Automatic (phone language)", "Automaticky (jazyk telefonu)", "Automatisch (Gerätesprache)"),
            "en" to "English", "cs" to "Čeština", "de" to "Deutsch").forEach { (key, name) ->
            settingsItem(if (language() == key) "✓" else "○", name,
                if (language() == key) translated("Selected", "Vybráno", "Ausgewählt") else "") {
                getSharedPreferences("community", MODE_PRIVATE).edit().putString("language", key).apply()
                openLanguageSettings()
            }
        }
    }
    private fun openAppearanceSettings() {
        scrollSettings(translated("Appearance", "Vzhled", "Darstellung")) { openCommunitySettings() }
        settingsSection(translated("THEME", "MOTIV", "DESIGN"))
        settingsItem("◐", translated("Solana Dark", "Solana – tmavý", "Solana Dunkel"),
            translated("Active theme", "Aktivní motiv", "Aktives Design")) { }
        text(translated("The dark Solana theme is currently the app's default design.",
            "Tmavý motiv Solana je aktuálně výchozí vzhled aplikace.",
            "Das dunkle Solana-Design ist derzeit die Standarddarstellung."), 13)
        settingsSection(translated("PHOTO GALLERY", "GALERIE FOTEK", "FOTOGALERIE"))
        settingsItem("▦", translated("Photo layout", "Rozložení fotek", "Fotoansicht"),
            translated("Choose thumbnail size", "Zvolit velikost náhledů", "Vorschaugröße wählen")) {
            val options = arrayOf(translated("Large thumbnails", "Velké náhledy", "Große Vorschau"),
                translated("Small thumbnails", "Malé náhledy", "Kleine Vorschau"))
            AlertDialog.Builder(this).setTitle(translated("Photo layout", "Rozložení fotek", "Fotoansicht"))
                .setSingleChoiceItems(options, if (photoLayout() == "large") 0 else 1) { dialog, index ->
                    getSharedPreferences("explorer", MODE_PRIVATE).edit().putString("photo_layout", if (index == 0) "large" else "small").apply()
                    dialog.dismiss(); openAppearanceSettings()
                }.setNegativeButton(translated("Cancel", "Zrušit", "Abbrechen"), null).show()
        }
    }
    private fun openFileSettings() {
        scrollSettings(translated("File browsing", "Procházení souborů", "Dateiansicht")) { openCommunitySettings() }
        settingsSection(translated("LOCATIONS", "UMÍSTĚNÍ", "SPEICHERORTE"))
        settingsItem("▤", translated("Browse phone", "Procházet telefon", "Telefon durchsuchen"),
            translated("Internal storage", "Interní úložiště", "Interner Speicher")) { openPhone() }
        settingsItem("▧", translated("Choose a folder", "Vybrat složku", "Ordner auswählen"),
            translated("Grant access to a folder", "Povolit přístup ke složce", "Ordnerzugriff erlauben")) { pickTree() }
    }
    private fun openStorageSettings() {
        scrollSettings(translated("Storage", "Úložiště", "Speicher")) { openCommunitySettings() }
        val storage = Environment.getExternalStorageDirectory()
        val total = storage.totalSpace.coerceAtLeast(1L)
        val used = (total - storage.freeSpace).coerceAtLeast(0L)
        val gb = 1024.0 * 1024 * 1024
        settingsSection(translated("INTERNAL STORAGE", "INTERNÍ ÚLOŽIŠTĚ", "INTERNER SPEICHER"))
        text(String.format(Locale.US, "%.1f GB / %.1f GB", used / gb, total / gb), 20)
        root.addView(ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal).apply {
            max = 100; progress = ((used * 100) / total).toInt()
            progressTintList = android.content.res.ColorStateList.valueOf(accent)
        }, LinearLayout.LayoutParams(-1, dp(9)))
        text(String.format(Locale.US, "%.1f GB %s", (total - used) / gb,
            translated("available", "volných", "frei")))
        settingsItem("▤", translated("Open storage", "Otevřít úložiště", "Speicher öffnen"), "") { openPhone() }
    }
    private fun openAboutSettings() {
        scrollSettings(translated("About the app", "O aplikaci", "Über die App")) { openCommunitySettings() }
        settingsSection("FILE EXPLORER COMMUNITY")
        text("Version 3.9 • Solana Style", 18)
        text(translated("Free Android file manager without ads.", "Bezplatný správce souborů pro Android bez reklam.",
            "Kostenloser Android-Dateimanager ohne Werbung."))
    }
    private fun showDonate() {
        screen(translated("Support development", "Podpořit vývoj", "Entwicklung unterstützen"))
        action("← " + translated("Settings", "Nastavení", "Einstellungen")) { openCommunitySettings() }
        text(translated("File Explorer is free and ad-free. Contributions are entirely optional.",
            "File Explorer je zdarma a bez reklam. Příspěvky jsou zcela dobrovolné.",
            "File Explorer ist kostenlos und werbefrei. Beiträge sind freiwillig."))
        action("♥  " + translated("Donate by card / Google Pay (Ko-fi)",
            "Přispět kartou / Google Pay (Ko-fi)",
            "Mit Karte / Google Pay spenden (Ko-fi)")) {
            try { startActivity(Intent(Intent.ACTION_VIEW, Uri.parse(donationPageUrl))) }
            catch (_: Exception) { message(translated("Cannot open Ko-fi", "Nelze otevřít Ko-fi", "Ko-fi kann nicht geöffnet werden")) }
        }
        action("◎  " + translated("Donate SOL – QR code and address", "Přispět SOL – QR kód a adresa",
            "SOL spenden – QR-Code und Adresse")) { showSolanaDonation() }
        text(translated("Card and wallet payments are handled outside this app.",
            "Platby kartou a peněženkou probíhají mimo tuto aplikaci.",
            "Karten- und Wallet-Zahlungen erfolgen außerhalb dieser App."), 12)
    }

    private fun showSolanaDonation() {
        val qrSize = dp(240)
        val layout = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(18), dp(14), dp(18), dp(8))
        }
        try {
            val matrix = com.google.zxing.qrcode.QRCodeWriter().encode(
                donationSolanaAddress, com.google.zxing.BarcodeFormat.QR_CODE, 512, 512)
            val bitmap = Bitmap.createBitmap(512, 512, Bitmap.Config.ARGB_8888)
            for (y in 0 until 512) for (x in 0 until 512) {
                bitmap.setPixel(x, y, if (matrix[x, y]) Color.BLACK else Color.WHITE)
            }
            layout.addView(ImageView(this).apply {
                setImageBitmap(bitmap)
                setBackgroundColor(Color.WHITE)
                scaleType = ImageView.ScaleType.FIT_CENTER
            }, LinearLayout.LayoutParams(-1, qrSize))
        } catch (_: Exception) { /* Address remains available as text and copy action. */ }
        layout.addView(TextView(this).apply {
            text = donationSolanaAddress
            setTextIsSelectable(true)
            textSize = 13f
            setTextColor(Color.BLACK)
            setPadding(0, dp(12), 0, dp(8))
        })
        AlertDialog.Builder(this)
            .setTitle(translated("Solana (SOL) donation", "Příspěvek Solana (SOL)", "Solana (SOL) Spende"))
            .setView(layout)
            .setPositiveButton(translated("Copy address", "Kopírovat adresu", "Adresse kopieren")) { _, _ ->
                (getSystemService(CLIPBOARD_SERVICE) as android.content.ClipboardManager)
                    .setPrimaryClip(android.content.ClipData.newPlainText("Solana donation address", donationSolanaAddress))
                message(translated("Address copied", "Adresa zkopírována", "Adresse kopiert"))
            }
            .setNegativeButton(translated("Close", "Zavřít", "Schließen"), null)
            .show()
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.statusBarColor = Color.rgb(17, 21, 30)
        window.navigationBarColor = Color.rgb(17, 21, 30)
        window.decorView.systemUiVisibility = 0
        val prefs = getSharedPreferences("explorer", MODE_PRIVATE)
        prefs.getString("tree", null)?.let { uri ->
            try { localRoot = DocumentFile.fromTreeUri(this, Uri.parse(uri)); local = localRoot } catch (_: Exception) {}
        }
        home()
    }
    private val bg = Color.rgb(5, 9, 17)
    private val panel = Color.rgb(18, 24, 40)
    private val ink = Color.rgb(238, 244, 252)
    private val muted = Color.rgb(159, 174, 196)
    private val accent = Color.rgb(32, 235, 211)
    private val solPurple = Color.rgb(166, 63, 243)
    private fun dp(n: Int) = (n * resources.displayMetrics.density).toInt()
    private fun shape(color: Int, radius: Int = 15) = GradientDrawable().apply {
        setColor(color); cornerRadius = dp(radius).toFloat()
    }
    private fun solGradient(radius: Int = 18) = GradientDrawable(
        GradientDrawable.Orientation.LEFT_RIGHT,
        intArrayOf(Color.rgb(7, 104, 113), Color.rgb(81, 32, 129), Color.rgb(155, 25, 173))
    ).apply { cornerRadius = dp(radius).toFloat(); setStroke(dp(1), accent) }
    private fun solCard() = GradientDrawable(
        GradientDrawable.Orientation.TL_BR,
        intArrayOf(Color.rgb(38, 21, 67), Color.rgb(12, 27, 41))
    ).apply { cornerRadius = dp(18).toFloat(); setStroke(dp(1), Color.rgb(85, 61, 122)) }
    private fun label(value: String, size: Int = 15, color: Int = ink, bold: Boolean = false) = TextView(this).apply {
        text = value; textSize = size.toFloat(); setTextColor(color)
        if (bold) setTypeface(null, Typeface.BOLD)
        gravity = Gravity.CENTER_VERTICAL
    }
    // Consistent vector-style pictograms; no device-dependent emoji or Unicode glyphs.
    private fun pictogram(kind: String, tint: Int, size: Int = 26): View = object : View(this) {
        private val pen = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            color = tint; style = Paint.Style.STROKE; strokeWidth = 2.3f
            strokeCap = Paint.Cap.ROUND; strokeJoin = Paint.Join.ROUND
        }
        override fun onDraw(canvas: Canvas) {
            super.onDraw(canvas)
            val scale = minOf(width, height) / 32f
            canvas.save(); canvas.translate((width - 32f * scale) / 2, (height - 32f * scale) / 2)
            canvas.scale(scale, scale)
            fun line(x: Float, y: Float, xx: Float, yy: Float) = canvas.drawLine(x,y,xx,yy,pen)
            fun box(x: Float,y: Float,xx: Float,yy: Float,r: Float=3f) = canvas.drawRoundRect(RectF(x,y,xx,yy),r,r,pen)
            fun path(vararg pts: Float) { val q=Path(); q.moveTo(pts[0],pts[1]); var i=2; while(i<pts.size){q.lineTo(pts[i],pts[i+1]);i+=2}; canvas.drawPath(q,pen) }
            when(kind) {
                "photos" -> { box(4f,6f,28f,26f); canvas.drawCircle(22f,12f,2f,pen); path(6f,23f,13f,16f,18f,21f,21f,18f,27f,24f) }
                "video" -> { box(4f,7f,28f,25f); path(13f,12f,21f,16f,13f,20f,13f,12f) }
                "audio" -> { line(18f,7f,18f,22f);line(18f,7f,26f,5f);line(26f,5f,26f,20f); canvas.drawOval(RectF(9f,20f,18f,26f),pen);canvas.drawOval(RectF(17f,18f,26f,24f),pen) }
                "documents" -> { path(8f,4f,20f,4f,26f,10f,26f,28f,8f,28f,8f,4f);path(20f,4f,20f,10f,26f,10f);line(12f,16f,22f,16f);line(12f,21f,22f,21f) }
                "downloads" -> { line(16f,5f,16f,22f);path(9f,16f,16f,23f,23f,16f);path(6f,24f,6f,28f,26f,28f,26f,24f) }
                "files" -> {path(3f,10f,3f,26f,29f,26f,29f,12f,16f,12f,12f,8f,3f,8f,3f,10f);line(3f,14f,29f,14f)}
                "scans" -> {path(5f,12f,5f,6f,11f,6f);path(21f,6f,27f,6f,27f,12f);path(5f,20f,5f,26f,11f,26f);path(21f,26f,27f,26f,27f,20f);line(8f,16f,24f,16f)}
                "shots" -> {box(5f,5f,27f,27f);box(10f,10f,22f,22f);canvas.drawCircle(17f,15f,1.5f,pen)}
                "network" -> {canvas.drawCircle(16f,7f,3f,pen);canvas.drawCircle(7f,24f,3f,pen);canvas.drawCircle(25f,24f,3f,pen);line(14f,10f,9f,21f);line(18f,10f,23f,21f);line(10f,24f,22f,24f)}
                "zip" -> {box(7f,4f,25f,28f);line(16f,7f,16f,20f);box(13f,20f,19f,25f,1f)}
                "star" -> {path(16f,4f,20f,12f,29f,13f,22f,20f,24f,29f,16f,24f,8f,29f,10f,20f,3f,13f,12f,12f,16f,4f)}
                "settings" -> {canvas.drawCircle(16f,16f,7f,pen);canvas.drawCircle(16f,16f,2.5f,pen);line(16f,4f,16f,8f);line(16f,24f,16f,28f);line(4f,16f,8f,16f);line(24f,16f,28f,16f)}
                "folder" -> {path(3f,10f,3f,26f,29f,26f,29f,12f,16f,12f,12f,8f,3f,8f,3f,10f)}
                else -> { box(6f,6f,26f,26f); line(11f,16f,21f,16f) }
            }
            canvas.restore()
        }
    }
    private fun homeMenu(anchor: View) {
        val popup = PopupWindow(this)
        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(9), dp(9), dp(9), dp(9))
            background = solCard()
        }
        val entries = listOf(
            Triple("settings", translated("Settings", "Nastavení", "Einstellungen"), { openCommunitySettings() }),
            Triple("network", translated("Network (SMB)", "Síť (SMB)", "Netzwerk (SMB)"), { smbConnections() }),
            Triple("folder", translated("Choose a folder", "Vybrat složku", "Ordner auswählen"), { pickTree() }),
            Triple("zip", translated("ZIP manager", "Správce ZIP", "ZIP-Verwaltung"), { openZipManager() }),
            Triple("settings", translated("Support development", "Podpořit vývoj", "Entwicklung unterstützen"), { showDonate() }),
            Triple("documents", translated("About", "O aplikaci", "Über die App"), { openAboutSettings() })
        )
        entries.forEachIndexed { i, (symbol, title, task) ->
            val item = LinearLayout(this).apply {
                gravity = Gravity.CENTER_VERTICAL
                orientation = LinearLayout.HORIZONTAL
                setPadding(dp(12), dp(4), dp(9), dp(4))
                addView(pictogram(symbol, if (i % 2 == 0) accent else Color.rgb(169, 132, 247)), LinearLayout.LayoutParams(dp(27), dp(27)))
                addView(label(title, 14, ink, true).apply { setPadding(dp(13), 0, 0, 0) }, LinearLayout.LayoutParams(0, -1, 1f))
                setOnClickListener { popup.dismiss(); task() }
            }
            container.addView(item, LinearLayout.LayoutParams(-1, dp(49)))
            if (i != entries.lastIndex) container.addView(View(this).apply { setBackgroundColor(Color.rgb(41, 47, 65)) }, LinearLayout.LayoutParams(-1, dp(1)))
        }
        popup.contentView = container
        popup.width = minOf(resources.displayMetrics.widthPixels - dp(38), dp(288))
        popup.height = -2
        popup.isFocusable = true
        popup.isOutsideTouchable = true
        popup.elevation = dp(14).toFloat()
        popup.setBackgroundDrawable(android.graphics.drawable.ColorDrawable(Color.TRANSPARENT))
        popup.showAsDropDown(anchor, 0, dp(4), Gravity.START)
    }

    private val favoritesPrefs get() = getSharedPreferences("favorite_folders", MODE_PRIVATE)
    private fun favoritePaths(): List<String> = favoritesPrefs.getString("paths", "")!!
        .split("\n").filter { it.isNotBlank() && File(it).isDirectory }
    private fun setFavorite(file: File) {
        val paths = favoritePaths().toMutableList()
        if (file.absolutePath in paths) paths.remove(file.absolutePath) else paths.add(file.absolutePath)
        favoritesPrefs.edit().putString("paths", paths.joinToString("\n")).apply()
        message(if (file.absolutePath in paths) translated("Added to favorites", "Přidáno do oblíbených", "Zu Favoriten hinzugefügt") else translated("Removed from favorites", "Odebráno z oblíbených", "Aus Favoriten entfernt"))
    }
    private fun showFavoriteFolders() {
        scrollSettings(translated("Favorite folders", "Oblíbené složky", "Favoriten")) { home() }
        val paths = favoritePaths()
        if (paths.isEmpty()) text(translated("Open any folder in All files and use the star to add it here.", "Otevři složku v Všechny soubory a pomocí hvězdičky ji přidej sem.", "Ordner öffnen und mit Stern markieren."))
        paths.forEach { path ->
            val folder = File(path)
            settingsItem("★", folder.name.ifEmpty { path }, path) { phoneDir = folder; openPhone() }
        }
    }

    private val zipSelectRequest = 7301
    private val zipSaveRequest = 7302
    private val zipOpenRequest = 7303
    private val zipDestinationRequest = 7304
    private var zipSelectedUris: List<Uri> = emptyList()
    private var zipArchiveUri: Uri? = null
    private fun openZipManager() {
        scrollSettings(translated("ZIP manager", "Správce ZIP", "ZIP-Verwaltung")) { openCommunitySettings() }
        settingsSection(translated("ARCHIVES", "ARCHIVY", "ARCHIVE"))
        settingsItem("+", translated("Create ZIP", "Vytvořit ZIP", "ZIP erstellen"), translated("Choose files to compress", "Vyber soubory ke kompresi", "Dateien auswählen")) {
            startActivityForResult(Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
                type = "*/*"; addCategory(Intent.CATEGORY_OPENABLE); putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
            }, zipSelectRequest)
        }
        settingsItem("↧", translated("Extract ZIP", "Rozbalit ZIP", "ZIP entpacken"), translated("Choose archive and destination", "Vyber archiv a cílovou složku", "Archiv und Zielordner wählen")) {
            startActivityForResult(Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
                type = "application/zip"; addCategory(Intent.CATEGORY_OPENABLE)
            }, zipOpenRequest)
        }
        text(translated("ZIP files are processed locally on your phone.", "ZIP soubory se zpracovávají přímo v telefonu.", "ZIP-Dateien werden lokal verarbeitet."), 13)
    }
    private fun createZip(target: Uri, sources: List<Uri>) {
        io.execute {
            try {
                contentResolver.openOutputStream(target, "w")!!.use { out ->
                    ZipOutputStream(out).use { zip ->
                        val used = mutableSetOf<String>()
                        sources.forEachIndexed { index, uri ->
                            val original = queryDisplayName(uri)?.takeIf { it.isNotBlank() } ?: "file_${index+1}"
                            val safe = original.replace('/', '_').replace('\\', '_')
                            var name = safe; var suffix = 2
                            while (!used.add(name)) { name = "${safe.substringBeforeLast('.', safe)}_${suffix++}" + if ('.' in safe) ".${safe.substringAfterLast('.')}" else "" }
                            zip.putNextEntry(ZipEntry(name))
                            contentResolver.openInputStream(uri)!!.use { it.copyTo(zip) }
                            zip.closeEntry()
                        }
                    }
                }
                runOnUiThread { message(translated("ZIP created", "ZIP vytvořen", "ZIP erstellt")); openZipManager() }
            } catch (e: Exception) { runOnUiThread { message("ZIP: ${e.message}") } }
        }
    }
    private fun extractZip(source: Uri, tree: Uri) {
        io.execute {
            try {
                val base = DocumentFile.fromTreeUri(this, tree) ?: error("Folder not available")
                var count = 0
                contentResolver.openInputStream(source)!!.use { input ->
                    ZipInputStream(input).use { zip ->
                        while (true) {
                            val entry = zip.nextEntry ?: break
                            val parts = entry.name.replace('\\', '/').split('/').filter { it.isNotBlank() }
                            // Prevent traversal, absolute paths and unsafe ZIP entries.
                            if (parts.isEmpty() || parts.any { it == ".." || it == "." || ':' in it }) { zip.closeEntry(); continue }
                            if (++count > 10000) error("Too many ZIP entries")
                            var folder = base
                            parts.dropLast(1).forEach { segment ->
                                folder = folder.findFile(segment)?.takeIf { it.isDirectory } ?: folder.createDirectory(segment) ?: error("Cannot create directory")
                            }
                            if (entry.isDirectory) {
                                val last = parts.last()
                                if (folder.findFile(last) == null) folder.createDirectory(last) ?: error("Cannot create directory")
                            } else {
                                val filename = parts.last()
                                if (folder.findFile(filename) != null) error("File already exists: $filename")
                                val mime = MimeTypeMap.getSingleton().getMimeTypeFromExtension(filename.substringAfterLast('.', "").lowercase()) ?: "application/octet-stream"
                                val file = folder.createFile(mime, filename) ?: error("Cannot create $filename")
                                contentResolver.openOutputStream(file.uri, "w")!!.use { output ->
                                    val buffer = ByteArray(8192)
                                    var written = 0L
                                    while (true) {
                                        val n = zip.read(buffer)
                                        if (n < 0) break
                                        written += n
                                        if (written > 2L * 1024 * 1024 * 1024) error("ZIP entry too large")
                                        output.write(buffer, 0, n)
                                    }
                                }
                            }
                            zip.closeEntry()
                        }
                    }
                }
                runOnUiThread { message(translated("ZIP extracted", "ZIP rozbalen", "ZIP entpackt")); openZipManager() }
            } catch (e: Exception) { runOnUiThread { message("ZIP: ${e.message}") } }
        }
    }

    private fun screen(title: String) {
        root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(bg)
            setPadding(dp(16), dp(12), dp(16), dp(12))
        }
        setContentView(root)
        if (Build.VERSION.SDK_INT >= 30) {
            root.setOnApplyWindowInsetsListener { view, insets ->
                val bars = insets.getInsets(WindowInsets.Type.systemBars())
                view.setPadding(dp(16), dp(12) + bars.top, dp(16), dp(12) + bars.bottom)
                insets
            }
            root.requestApplyInsets()
        }
        val heading = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL }
        val logo = label("≋", 32, accent, true).apply {
            gravity = Gravity.CENTER_VERTICAL
            if (title == "File Explorer") {
                contentDescription = translated("Open menu", "Otevřít nabídku", "Menü öffnen")
                setOnClickListener { homeMenu(this) }
            }
        }
        heading.addView(logo, LinearLayout.LayoutParams(dp(42), dp(56)))
        heading.addView(label(title.removePrefix("📁 ").removePrefix("📱 ").removePrefix("🖥️ "), 25, ink, true), LinearLayout.LayoutParams(0, dp(56), 1f))
        root.addView(heading)
    }
    private fun text(value: String, size: Int = 15) {
        root.addView(label(value, size, muted).apply { setPadding(dp(4), dp(8), dp(4), dp(10)) })
    }
    private fun action(title: String, click: () -> Unit) {
        val item = label(title, 15, ink, true).apply {
            gravity = Gravity.CENTER_VERTICAL
            setPadding(dp(17), 0, dp(12), 0)
            background = solCard()
            setOnClickListener { click() }
        }
        root.addView(item, LinearLayout.LayoutParams(-1, dp(51)).apply { bottomMargin = dp(8) })
    }
    private fun destinationCard(symbol: String, title: String, subtitle: String, click: () -> Unit) {
        val card = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(dp(14), dp(12), dp(14), dp(12))
            background = solCard()
            setOnClickListener { click() }
        }
        val iconView = TextView(this).apply {
            text = symbol
            textSize = 35f
            setTextColor(ink)
            setTypeface(null, Typeface.BOLD)
            gravity = Gravity.CENTER
            background = shape(Color.rgb(43, 59, 81), 15)
        }
        card.addView(iconView, LinearLayout.LayoutParams(dp(72), dp(72)))
        val details = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(dp(15), 0, 0, 0)
        }
        details.addView(label(title, 19, ink, true))
        details.addView(label(subtitle, 12, muted))
        card.addView(details, LinearLayout.LayoutParams(0, -2, 1f))
        card.addView(label("›", 30, accent, true))
        root.addView(card, LinearLayout.LayoutParams(-1, dp(98)).apply { bottomMargin = dp(11) })
    }

    private fun field(hintText: String, secret: Boolean = false): EditText = EditText(this).apply {
        hint = hintText; setHintTextColor(muted); setTextColor(ink)
        if (secret) inputType = android.text.InputType.TYPE_CLASS_TEXT or android.text.InputType.TYPE_TEXT_VARIATION_PASSWORD
        root.addView(this)
    }
    private fun entries(rows: List<Pair<String, () -> Unit>>, longPress: ((Int) -> Unit)? = null) {
        val scroll = ScrollView(this).apply { isFillViewport = true }
        val content = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        rows.forEachIndexed { index, (name, click) ->
            val folder = name.startsWith("📁")
            val display = name.removePrefix("📁 ").removePrefix("📄 ")
            val line = LinearLayout(this).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                background = shape(panel, 12)
                setPadding(dp(13), dp(3), dp(12), dp(3))
                setOnClickListener { click() }
                if (longPress != null) setOnLongClickListener { longPress(index); true }
            }
            line.addView(label(if (folder) "📁" else when(display.substringAfterLast('.', "").lowercase()) {
                "jpg", "jpeg", "png", "webp", "gif" -> "🖼️"
                "mp4", "mkv", "mov" -> "🎬"
                "mp3", "wav", "flac" -> "🎵"
                "pdf" -> "📕"
                "zip", "rar", "7z" -> "🗜️"
                else -> "📄"
            }, 22), LinearLayout.LayoutParams(dp(43), -1))
            line.addView(label(display, 15, ink, true).apply { maxLines = 2; ellipsize = android.text.TextUtils.TruncateAt.END }, LinearLayout.LayoutParams(0, -2, 1f))
            line.addView(label("⋮", 22, muted), LinearLayout.LayoutParams(dp(22), -1))
            content.addView(line, LinearLayout.LayoutParams(-1, dp(62)).apply { bottomMargin = dp(7) })
        }
        scroll.addView(content)
        root.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1f))
    }
    private fun quickTile(symbol: String, name: String, click: () -> Unit): LinearLayout {
        return LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.CENTER
            background = shape(panel)
            addView(label(symbol, 25, accent).apply { gravity = Gravity.CENTER })
            addView(label(name, 12, ink, true).apply { gravity = Gravity.CENTER })
            setOnClickListener { click() }
        }
    }
    private fun showCategory(directory: String) {
        phoneDir = File(Environment.getExternalStorageDirectory(), directory)
        openPhone()
    }
    private fun message(s: String) = Toast.makeText(this, s, Toast.LENGTH_LONG).show()
    private fun ask(title: String, initial: String = "", result: (String) -> Unit) {
        val input = EditText(this).apply { setSingleLine(); setText(initial) }
        AlertDialog.Builder(this).setTitle(title).setView(input)
            .setPositiveButton("Potvrdit") { _, _ -> input.text.toString().trim().takeIf { it.isNotEmpty() }?.let(result) }
            .setNegativeButton(translated("Cancel", "Zrušit", "Abbrechen"), null).show()
    }
    private fun confirm(title: String, yes: () -> Unit) {
        AlertDialog.Builder(this).setMessage(title).setPositiveButton("Ano") { _, _ -> yes() }
            .setNegativeButton("Ne", null).show()
    }
    private fun home() {
        mode = "home"; selectionMode = false; selectedFiles.clear()
        screen("File Explorer")
        val fixedRoot = root
        val scroll = ScrollView(this).apply { isFillViewport = true; clipToPadding = false }
        val content = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        scroll.addView(content)
        fixedRoot.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1f))
        root = content

        val search = EditText(this).apply {
            setSingleLine(true)
            hint = "⌕  " + translated("Search your phone...", "Hledat v telefonu...", "Telefon durchsuchen...")
            textSize = 15f; setTextColor(ink); setHintTextColor(muted)
            background = solCard(); setPadding(dp(18), 0, dp(18), 0)
            setOnEditorActionListener { _, _, _ ->
                val query = text.toString().trim()
                if (query.isNotEmpty()) searchPhone(query)
                true
            }
        }
        root.addView(search, LinearLayout.LayoutParams(-1, dp(52)).apply { bottomMargin = dp(16) })

        val storage = Environment.getExternalStorageDirectory()
        val total = storage.totalSpace.coerceAtLeast(1L)
        val used = (total - storage.freeSpace).coerceAtLeast(0L)
        val gb = 1024.0 * 1024 * 1024
        val storageCard = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL; setPadding(dp(18), dp(16), dp(18), dp(16))
            background = solCard(); setOnClickListener { openPhone() }
        }
        storageCard.addView(label("▣  " + translated("Internal storage", "Interní úložiště", "Interner Speicher") + "   ›", 18, ink, true))
        storageCard.addView(label(String.format(Locale.US, "%.1f GB / %.1f GB", used / gb, total / gb), 13, muted))
        storageCard.addView(ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal).apply {
            max = 100; progress = ((used * 100) / total).toInt()
            progressTintList = android.content.res.ColorStateList.valueOf(accent)
            progressBackgroundTintList = android.content.res.ColorStateList.valueOf(Color.rgb(49, 53, 74))
        }, LinearLayout.LayoutParams(-1, dp(8)).apply { topMargin = dp(12) })
        root.addView(storageCard, LinearLayout.LayoutParams(-1, -2).apply { bottomMargin = dp(16) })

        text(translated("YOUR FILES", "VAŠE SOUBORY", "DEINE DATEIEN"), 12)
        val categories = listOf(
            Triple("photos", translated("Photos", "Fotky", "Fotos"), "photos"),
            Triple("video", translated("Videos", "Videa", "Videos"), "video"),
            Triple("audio", translated("Music", "Hudba", "Musik"), "audio"),
            Triple("documents", translated("Documents", "Dokumenty", "Dokumente"), "documents"),
            Triple("downloads", translated("Downloads", "Stažené", "Downloads"), "downloads"),
            Triple("files", translated("All files", "Všechny soubory", "Alle Dateien"), "files")
        )
        val tileColors = listOf(
            Color.rgb(176, 125, 255), Color.rgb(250, 120, 151), Color.rgb(52, 220, 196),
            Color.rgb(100, 160, 255), Color.rgb(250, 189, 91), Color.rgb(170, 140, 255)
        )
        categories.chunked(2).forEachIndexed { rowIndex, group ->
            val line = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
            group.forEachIndexed { colIndex, (kind, name, target) ->
                val tint = tileColors[rowIndex * 2 + colIndex]
                val tile = LinearLayout(this).apply {
                    orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
                    background = shape(Color.rgb(18, 24, 40), 17)
                    setPadding(dp(12), dp(9), dp(8), dp(9))
                    val iconHolder = android.widget.FrameLayout(this@MainActivity).apply {
                        background = shape(Color.argb(37, Color.red(tint), Color.green(tint), Color.blue(tint)), 13)
                        addView(pictogram(kind, tint), android.widget.FrameLayout.LayoutParams(dp(31),dp(31),Gravity.CENTER))
                    }
                    addView(iconHolder, LinearLayout.LayoutParams(dp(47),dp(47)))
                    addView(label(name, 14, ink, true).apply {
                        setPadding(dp(10),0,0,0); maxLines=2
                    }, LinearLayout.LayoutParams(0,-2,1f))
                    setOnClickListener {
                        when (target) {
                            "photos" -> showAllPhotos()
                            "video", "audio", "documents" -> showMediaGallery(target)
                            "downloads" -> showCategory("Download")
                            else -> openPhone()
                        }
                    }
                }
                line.addView(tile, LinearLayout.LayoutParams(0,dp(72),1f).apply { if(colIndex==0) marginEnd=dp(9) })
            }
            root.addView(line, LinearLayout.LayoutParams(-1,-2).apply { bottomMargin=dp(9) })
        }
        text(translated("QUICK ACCESS", "RYCHLÝ PŘÍSTUP", "SCHNELLZUGRIFF"), 12)
        val shortcuts = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
        listOf(
            Triple("scans", translated("My scans", "Moje skeny", "Meine Scans"), "scans"),
            Triple("shots", translated("Screenshots", "Snímky obrazovky", "Screenshots"), "shots")
        ).forEachIndexed { index, (kind, title, target) ->
            val tile = LinearLayout(this).apply {
                orientation=LinearLayout.HORIZONTAL; gravity=Gravity.CENTER_VERTICAL
                background=shape(panel,16); setPadding(dp(13),0,dp(8),0)
                addView(pictogram(kind,accent),LinearLayout.LayoutParams(dp(30),dp(30)))
                addView(label(title,13,ink,true).apply {setPadding(dp(10),0,0,0)},LinearLayout.LayoutParams(0,-2,1f))
                setOnClickListener { if(target=="scans") showScans() else showScreenshots() }
            }
            shortcuts.addView(tile,LinearLayout.LayoutParams(0,dp(60),1f).apply {if(index==0) marginEnd=dp(9)})
        }
        root.addView(shortcuts,LinearLayout.LayoutParams(-1,-2).apply {bottomMargin=dp(13)})
        val fav = LinearLayout(this).apply {
            orientation=LinearLayout.HORIZONTAL; gravity=Gravity.CENTER_VERTICAL
            background=shape(panel,16); setPadding(dp(15),0,dp(12),0)
            addView(pictogram("star",Color.rgb(245,190,82)),LinearLayout.LayoutParams(dp(30),dp(30)))
            addView(label(translated("Favorites", "Oblíbené složky", "Favoriten"),14,ink,true).apply {setPadding(dp(12),0,0,0)},LinearLayout.LayoutParams(0,-2,1f))
            addView(label("›",23,muted))
            setOnClickListener { showFavoriteFolders() }
        }
        root.addView(fav, LinearLayout.LayoutParams(-1,dp(60)).apply {bottomMargin=dp(13)})
        text(translated("TOOLS", "NÁSTROJE", "WERKZEUGE"),12)
        val scanner = LinearLayout(this).apply {
            orientation=LinearLayout.HORIZONTAL; gravity=Gravity.CENTER_VERTICAL
            background=shape(panel,16);setPadding(dp(16),0,dp(14),0)
            addView(pictogram("scans",Color.rgb(160,124,249)),LinearLayout.LayoutParams(dp(30),dp(30)))
            addView(label(translated("Scan a document", "Skenovat dokument", "Dokument scannen"),15,ink,true).apply {setPadding(dp(12),0,0,0)},LinearLayout.LayoutParams(0,-2,1f))
            addView(label("›",23,muted).apply {gravity=Gravity.RIGHT},LinearLayout.LayoutParams(0,-2,1f))
            setOnClickListener { startDocumentScanner() }
        }
        root.addView(scanner,LinearLayout.LayoutParams(-1,dp(59)).apply {bottomMargin=dp(10)})
        val network = LinearLayout(this).apply {
            orientation=LinearLayout.HORIZONTAL;gravity=Gravity.CENTER_VERTICAL
            background=shape(panel,16);setPadding(dp(16),0,dp(14),0)
            addView(pictogram("network",accent),LinearLayout.LayoutParams(dp(30),dp(30)))
            addView(label(translated("Network / Windows (SMB)","Síť / Windows (SMB)","Netzwerk / Windows (SMB)"),14,ink,true).apply {setPadding(dp(12),0,0,0)},LinearLayout.LayoutParams(0,-2,1f))
            addView(label("›",23,muted).apply {gravity=Gravity.RIGHT},LinearLayout.LayoutParams(0,-2,1f))
            setOnClickListener { smbConnections() }
        }
        root.addView(network,LinearLayout.LayoutParams(-1,dp(59)).apply {bottomMargin=dp(10)})
        if(share!=null) settingsItem("↩",shareName,"SMB") {showRemote()}
        val settingsRow = LinearLayout(this).apply {
            orientation=LinearLayout.HORIZONTAL;gravity=Gravity.CENTER_VERTICAL
            setPadding(dp(16),0,dp(14),0);background=shape(panel,16)
            addView(pictogram("settings",muted),LinearLayout.LayoutParams(dp(28),dp(28)))
            addView(label(translated("Settings", "Nastavení", "Einstellungen"),14,ink,true).apply {setPadding(dp(12),0,0,0)},LinearLayout.LayoutParams(0,-2,1f))
            setOnClickListener {openCommunitySettings()}
        }
        root.addView(settingsRow,LinearLayout.LayoutParams(-1,dp(54)).apply {bottomMargin=dp(14)})
        root = fixedRoot
    }

    // Fotografie se filtrují podle času pořízení, nikoliv podle názvu složky.
    // Pokud metadata pořízení chybí, použije se čas přidání do knihovny.
    private fun loadPhotos(onlyTenMinutes: Boolean): List<RecentPhoto> {
        val now = System.currentTimeMillis()
        val cutoff = now - 10 * 60 * 1000L
        val found = mutableListOf<RecentPhoto>()
        val projection = arrayOf(MediaStore.Images.Media._ID, MediaStore.Images.Media.DISPLAY_NAME,
            MediaStore.Images.Media.DATE_TAKEN, MediaStore.Images.Media.DATE_ADDED)
        val collection = MediaStore.Images.Media.EXTERNAL_CONTENT_URI
        try {
            contentResolver.query(collection, projection, null, null,
                "${MediaStore.Images.Media.DATE_ADDED} DESC")?.use { cursor ->
                val idCol = cursor.getColumnIndexOrThrow(MediaStore.Images.Media._ID)
                val nameCol = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.DISPLAY_NAME)
                val takenCol = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.DATE_TAKEN)
                val addedCol = cursor.getColumnIndexOrThrow(MediaStore.Images.Media.DATE_ADDED)
                while (cursor.moveToNext()) {
                    val taken = if (cursor.isNull(takenCol)) 0L else cursor.getLong(takenCol)
                    val added = cursor.getLong(addedCol) * 1000L
                    val timestamp = if (taken > 0L) taken else added
                    if (!onlyTenMinutes || timestamp in cutoff..now) {
                        found.add(RecentPhoto(ContentUris.withAppendedId(collection, cursor.getLong(idCol)),
                            cursor.getString(nameCol) ?: "Fotografie", timestamp))
                    }
                }
            }
        } catch (e: Exception) { message(translated("Unable to load photos: ${e.message}", "Fotografie nelze načíst: ${e.message}", "Unable to load photos: ${e.message}")) }
        return found.sortedByDescending { it.timestamp }
    }

    private fun showRecentPhotos() = showPhotoGallery("all")
    private fun showAllPhotos() {
        selectedPhotos.clear()
        allPhotosSelectionMode = false
        photoScrollIndex = 0
        showPhotoGallery("all")
    }

    private fun openPhoto(photo: RecentPhoto) = openMedia(photo, "all")

    private fun photoContextMenu(photo: RecentPhoto, which: String) {
        AlertDialog.Builder(this)
            .setTitle(photo.name)
            .setItems(arrayOf(translated("Open photo", "Otevřít fotografii", "Open photo"), translated("Select / deselect", "Označit / zrušit označení", "Select / deselect"), translated("Share photo", "Sdílet fotografii", "Share photo"), translated("Open with… (change app)", "Otevřít pomocí… (změnit aplikaci)", "Open with… (change app)"))) { _, choice ->
                when (choice) {
                    0 -> openPhoto(photo)
                    1 -> {
                        allPhotosSelectionMode = true
                        if (!selectedPhotos.add(photo.uri)) selectedPhotos.remove(photo.uri)
                        showPhotoGallery(which)
                    }
                    3 -> openMedia(photo, "all", true)
                    2 -> try {
                        startActivity(Intent.createChooser(Intent(Intent.ACTION_SEND).apply {
                            type = "image/*"
                            putExtra(Intent.EXTRA_STREAM, photo.uri)
                            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                        }, translated("Share photo", "Sdílet fotografii", "Share photo")))
                    } catch (_: Exception) { message(translated("Cannot share photo", "Fotografii nelze sdílet", "Cannot share photo")) }
                }
            }.show()
    }

    private fun deleteSelectedPhotos() {
        val targets = recentPhotos.filter { it.uri in selectedPhotos }.map { it.uri }
        if (targets.isEmpty()) { message(translated("Select photos first", "Nejdřív označ fotografie", "Select photos first")); return }
        confirm(translated("Are you sure you want to delete ${targets.size} selected photos from your phone?", "Opravdu smazat ${targets.size} vybraných fotografií z telefonu?", "Are you sure you want to delete ${targets.size} selected photos from your phone?")) {
            if (Build.VERSION.SDK_INT >= 30) {
                try {
                    pendingPhotoDeletion = targets
                    val request = MediaStore.createDeleteRequest(contentResolver, targets)
                    startIntentSenderForResult(request.intentSender, photoDeleteRequest, null, 0, 0, 0)
                } catch (e: Exception) {
                    pendingPhotoDeletion = emptyList()
                    message(translated("Cannot start deletion: ${e.message}", "Mazání nelze spustit: ${e.message}", "Cannot start deletion: ${e.message}"))
                }
            } else {
                var removed = 0
                targets.forEach { uri ->
                    try { if (contentResolver.delete(uri, null, null) > 0) removed++ }
                    catch (_: Exception) { }
                }
                selectedPhotos.clear()
                showPhotoGallery(photoScreen)
                message(translated("Deleted $removed z ${targets.size} photos", "Smazáno $removed z ${targets.size} fotografií", "Deleted $removed z ${targets.size} photos"))
            }
        }
    }

    // Ovládací prvky i spodní akce musí být dosažitelné posouváním celé stránky.
    private fun enableGalleryScrolling() {
        val container = root
        val scroll = ScrollView(this).apply {
            isFillViewport = false
            clipToPadding = false
        }
        val content = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        scroll.addView(content, android.widget.FrameLayout.LayoutParams(-1, -2))
        container.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1f))
        root = content
    }

    private fun showPhotoGallery(which: String) {
        if (photoScreen != which) photoScrollIndex = 0
        photoScreen = which
        mode = which
        screen(translated("All photos", "Všechny fotografie", "Alle Fotos"))
        enableGalleryScrolling()
        action(translated("← Home", "← Domů", "← Home")) { home() }
        // Na Androidu 13+ musí být povolené čtení obrázků; Android 14 může
        // nabídnout pouze vybrané snímky, pak se zobrazí jen zpřístupněné.
        val permission = if (Build.VERSION.SDK_INT >= 33) Manifest.permission.READ_MEDIA_IMAGES
            else Manifest.permission.READ_EXTERNAL_STORAGE
        if (checkSelfPermission(permission) != PackageManager.PERMISSION_GRANTED && !hasFullAccess()) {
            text(translated("Allow photo access to display thumbnails.", "Povol přístup k fotografiím, aby se zobrazily jejich náhledy.", "Allow photo access to display thumbnails."))
            action(translated("Allow photo access", "Povolit přístup k fotkám", "Allow photo access")) { requestPermissions(arrayOf(permission), 201) }
            return
        }
        recentPhotos = loadPhotos(false)
        selectedPhotos.retainAll(recentPhotos.map { it.uri }.toSet())
        text(translated("Available photos", "Dostupné fotografie", "Verfügbare Fotos") + " • ${recentPhotos.size}", 13)
        val chooser = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
        listOf(Triple(translated("▦ Large", "▦ Velké", "▦ Large"), "large", 0), Triple(translated("▥ Small", "▥ Malé", "▥ Small"), "small", 0), Triple(translated("☷ List", "☷ Seznam", "☷ Liste"), "list", 0)).forEach { (name, key, _) ->
            val active = photoLayout() == key
            val view = label(name, 13, if (active) Color.WHITE else muted, active).apply {
                gravity = Gravity.CENTER
                background = shape(if (active) Color.rgb(55, 99, 157) else panel, 10)
                setOnClickListener { setPhotoLayout(key) }
            }
            chooser.addView(view, LinearLayout.LayoutParams(0, dp(42), 1f).apply { marginEnd = dp(5) })
        }
        root.addView(chooser, LinearLayout.LayoutParams(-1, dp(42)).apply { bottomMargin = dp(10) })
        if (recentPhotos.isEmpty()) {
            text(translated("No photos to display. Try Refresh or check permissions.", "Žádné fotografie k zobrazení. Zkus Obnovit nebo zkontroluj oprávnění.", "No photos to display. Try Refresh or check permissions."))
            action(translated("↻ Refresh", "↻ Obnovit", "↻ Refresh")) { showPhotoGallery(which) }
            return
        }
        if (which == "recent" || allPhotosSelectionMode) action(if (selectedPhotos.size == recentPhotos.size) translated("☐ Deselect all", "☐ Zrušit výběr", "☐ Deselect all") else translated("☑ Select all (${recentPhotos.size})", "☑ Vybrat vše (${recentPhotos.size})", "☑ Select all (${recentPhotos.size})")) {
            if (selectedPhotos.size == recentPhotos.size) selectedPhotos.clear()
            else { selectedPhotos.clear(); selectedPhotos.addAll(recentPhotos.map { it.uri }) }
            showPhotoGallery(which)
        }
        if (which == "all" && allPhotosSelectionMode) {
            action(translated("✕ Exit selection", "✕ Ukončit výběr", "✕ Exit selection")) {
                allPhotosSelectionMode = false
                selectedPhotos.clear()
                showPhotoGallery(which)
            }
        }
        if (selectedPhotos.isNotEmpty()) {
            action(translated("📋 Copy selected (${selectedPhotos.size}) to phone folder", "📋 Kopírovat vybrané (${selectedPhotos.size}) do složky telefonu", "📋 Copy selected (${selectedPhotos.size}) to phone folder")) {
                photoClipboard = recentPhotos.filter { it.uri in selectedPhotos }
                selectedPhotos.clear()
                phoneDir = Environment.getExternalStorageDirectory()
                openPhone()
                message(translated("Open the destination folder and tap Paste photos here", "Otevři cílovou složku a klepni na Vložit fotografie sem", "Open the destination folder and tap Paste photos here"))
            }
            text(translated("SHARE SELECTED PHOTOS", "SDÍLET VYBRANÉ FOTOGRAFIE", "AUSGEWÄHLTE FOTOS TEILEN"), 13)
            listOf(
                Triple("💬", "WhatsApp", "com.whatsapp"),
                Triple("💬", "Messenger", "com.facebook.orca"),
                Triple("🎮", "Discord", "com.discord"),
                Triple("✉", "Gmail", "com.google.android.gm")
            ).forEach { (symbol, name, pkg) ->
                destinationCard(symbol, name, translated("Share selected photos", "Sdílet vybrané fotky", "Ausgewählte Fotos teilen")) {
                    shareSelectedPhotos(pkg)
                }
            }
            action(translated("More apps…", "Další aplikace…", "Weitere Apps…")) { shareSelectedPhotos() }
        }
        if (selectedPhotos.isNotEmpty()) {
            action(translated("🗑 Delete selected photos (${selectedPhotos.size})", "🗑 Smazat vybrané fotografie (${selectedPhotos.size})", "🗑 Delete selected photos (${selectedPhotos.size})")) { deleteSelectedPhotos() }
        }
        action(translated("↻ Refresh photos", "↻ Obnovit fotografie", "↻ Fotos aktualisieren")) { showPhotoGallery(which) }
        val grid = GridView(this).apply {
            numColumns = if (photoLayout() == "large") 2 else if (photoLayout() == "small") 3 else 1
            horizontalSpacing = dp(7)
            verticalSpacing = dp(7)
            stretchMode = GridView.STRETCH_COLUMN_WIDTH
            selector = android.graphics.drawable.ColorDrawable(Color.TRANSPARENT)
            clipToPadding = false
            adapter = object : BaseAdapter() {
                override fun getCount() = recentPhotos.size
                override fun getItem(position: Int): Any = recentPhotos[position]
                override fun getItemId(position: Int) = position.toLong()
                override fun getView(position: Int, convertView: View?, parent: ViewGroup): View {
                    val photo = recentPhotos[position]
                    val listMode = photoLayout() == "list"
                    val size = if (listMode) 62 else if (photoLayout() == "large") 154 else 104
                    val row = LinearLayout(this@MainActivity).apply {
                        orientation = if (listMode) LinearLayout.HORIZONTAL else LinearLayout.VERTICAL
                        gravity = Gravity.CENTER_VERTICAL
                        background = shape(if (photo.uri in selectedPhotos) Color.rgb(47, 85, 127) else panel, 12)
                        setPadding(dp(5), dp(5), dp(5), dp(5))
                        setOnClickListener {
                            if (which == "all" && !allPhotosSelectionMode) {
                                openPhoto(photo)
                            } else {
                                if (!selectedPhotos.add(photo.uri)) selectedPhotos.remove(photo.uri)
                                photoScrollIndex = (parent as? GridView)?.firstVisiblePosition ?: 0
                                showPhotoGallery(which)
                            }
                        }
                        if (which == "all") setOnLongClickListener {
                            photoScrollIndex = (parent as? GridView)?.firstVisiblePosition ?: 0
                            photoContextMenu(photo, which)
                            true
                        }
                    }
                    val thumbnail = ImageView(this@MainActivity).apply {
                        scaleType = ImageView.ScaleType.CENTER_CROP
                        setImageResource(android.R.drawable.ic_menu_gallery)
                        tag = photo.uri.toString()
                    }
                    row.addView(thumbnail, LinearLayout.LayoutParams(if (listMode) dp(size) else -1, dp(size)))
                    val detail = LinearLayout(this@MainActivity).apply {
                        orientation = LinearLayout.HORIZONTAL
                        gravity = Gravity.CENTER_VERTICAL
                        setPadding(dp(5), dp(5), dp(3), dp(2))
                    }
                    val formatter = SimpleDateFormat(if (listMode) "dd.MM.yyyy HH:mm" else "dd.MM. HH:mm", Locale.getDefault())
                    val title = if (listMode) "${photo.name}  •  ${formatter.format(Date(photo.timestamp))}"
                        else formatter.format(Date(photo.timestamp))
                    detail.addView(label(title, if (listMode) 12 else 11, ink), LinearLayout.LayoutParams(0, -2, 1f))
                    if (which == "recent" || allPhotosSelectionMode) {
                        detail.addView(label(if (photo.uri in selectedPhotos) "☑" else "☐", 21, accent))
                    }
                    row.addView(detail, LinearLayout.LayoutParams(if (listMode) 0 else -1, -2, if (listMode) 1f else 0f))
                    val key = photo.uri.toString()
                    val cached = thumbCache.get(key)
                    if (cached != null) thumbnail.setImageBitmap(cached)
                    else thumbnailPool.execute {
                        try {
                            val bitmap = contentResolver.loadThumbnail(photo.uri, Size(240, 240), null)
                            thumbCache.put(key, bitmap)
                            runOnUiThread { if (thumbnail.tag == key) thumbnail.setImageBitmap(bitmap) }
                        } catch (_: Exception) { }
                    }
                    return row
                }
            }
        }
        root.addView(grid, LinearLayout.LayoutParams(-1, dp(390)))
        grid.setSelection(photoScrollIndex)
    }

    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<out String>, grantResults: IntArray) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == 201) showPhotoGallery(photoScreen)
        if (requestCode == 202) showMediaGallery(mediaScreen)
        if (requestCode == 217) showScreenshots()
    }


    // Knihovny souborů z celého sdíleného úložiště, nikoliv pouze z Movies/Music/Documents.
    private fun loadMedia(kind: String): List<RecentPhoto> {
        val found = mutableListOf<RecentPhoto>()
        val collection = MediaStore.Files.getContentUri("external")
        val id = MediaStore.Files.FileColumns._ID
        val name = MediaStore.Files.FileColumns.DISPLAY_NAME
        val date = MediaStore.Files.FileColumns.DATE_MODIFIED
        val mime = MediaStore.Files.FileColumns.MIME_TYPE
        val mediaType = MediaStore.Files.FileColumns.MEDIA_TYPE
        val selection = when (kind) {
            "video" -> "$mediaType=?"
            "audio" -> "$mediaType=?"
            else -> "$mediaType=? AND ($mime LIKE ? OR $mime LIKE ? OR $mime LIKE ? OR $mime LIKE ? OR $mime LIKE ? OR $mime LIKE ? OR $mime LIKE ?)"
        }
        val args = when (kind) {
            "video" -> arrayOf(MediaStore.Files.FileColumns.MEDIA_TYPE_VIDEO.toString())
            "audio" -> arrayOf(MediaStore.Files.FileColumns.MEDIA_TYPE_AUDIO.toString())
            else -> arrayOf(MediaStore.Files.FileColumns.MEDIA_TYPE_NONE.toString(), "application/pdf", "application/msword", "application/vnd.%", "text/%", "application/rtf", "application/zip", "application/octet-stream")
        }
        try {
            contentResolver.query(collection, arrayOf(id, name, date, mime), selection, args, "$date DESC")?.use { c ->
                val idCol = c.getColumnIndexOrThrow(id)
                val nameCol = c.getColumnIndexOrThrow(name)
                val dateCol = c.getColumnIndexOrThrow(date)
                val mimeCol = c.getColumnIndexOrThrow(mime)
                while (c.moveToNext()) {
                    val filename = c.getString(nameCol) ?: continue
                    val fileMime = c.getString(mimeCol) ?: ""
                    if (kind == "documents" && !(fileMime.startsWith("application/pdf") || fileMime.startsWith("application/msword") || fileMime.startsWith("application/vnd.") || fileMime.startsWith("text/") || fileMime == "application/rtf" || fileMime == "application/zip" || filename.substringAfterLast('.', "").lowercase() in setOf("pdf","doc","docx","xls","xlsx","ppt","pptx","txt","csv","odt","ods","rtf","zip"))) continue
                    found.add(RecentPhoto(ContentUris.withAppendedId(collection, c.getLong(idCol)), filename, c.getLong(dateCol) * 1000L))
                }
            }
        } catch (_: Exception) { }
        // Na Androidu 11+ se dokumenty nemusí v MediaStore.Files objevit. Při
        // povoleném přístupu ke všem souborům je doplníme přímo z úložiště.
        if (kind == "documents" && hasFullAccess()) {
            val extensions = setOf("pdf","doc","docx","xls","xlsx","ppt","pptx","txt","csv","odt","ods","odp","rtf")
            val seen = found.map { it.name to it.timestamp }.toMutableSet()
            val stack = java.util.ArrayDeque<File>()
            stack.add(Environment.getExternalStorageDirectory())
            var visited = 0
            while (stack.isNotEmpty() && visited < 120000) {
                val f = stack.removeLast(); visited++
                if (f.isDirectory) {
                    if (f.name in setOf("Android", ".thumbnails")) continue
                    f.listFiles()?.forEach { stack.add(it) }
                } else if (f.extension.lowercase() in extensions && seen.add(f.name to f.lastModified())) {
                    found.add(RecentPhoto(Uri.fromFile(f), f.name, f.lastModified()))
                }
            }
        }
        return found.sortedByDescending { it.timestamp }
    }

    // Zapamatování preferované aplikace zvlášť pro příponu souboru.
    private fun mediaMime(item: RecentPhoto, kind: String): String {
        val ext = item.name.substringAfterLast('.', "").lowercase(Locale.ROOT)
        return MimeTypeMap.getSingleton().getMimeTypeFromExtension(ext)
            ?: contentResolver.getType(item.uri)
            ?: when (kind) { "video" -> "video/*"; "audio" -> "audio/*"; "all" -> "image/*"; else -> "application/octet-stream" }
    }
    private fun viewUri(item: RecentPhoto): Uri = if (item.uri.scheme == "file") {
        FileProvider.getUriForFile(this, "$packageName.provider", File(requireNotNull(item.uri.path)))
    } else item.uri
    private fun viewerKey(item: RecentPhoto, kind: String): String =
        "viewer_" + (item.name.substringAfterLast('.', "").lowercase(Locale.ROOT).ifBlank { kind })

    private fun openMedia(item: RecentPhoto, kind: String, choose: Boolean = false) {
        val uri = try { viewUri(item) } catch (_: Exception) { message(translated("File unavailable", "Soubor není dostupný", "File unavailable")); return }
        val mime = mediaMime(item, kind)
        val intent = Intent(Intent.ACTION_VIEW).apply {
            setDataAndType(uri, mime)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
        }
        val prefs = getSharedPreferences("explorer", MODE_PRIVATE)
        val key = viewerKey(item, kind)
        val saved = prefs.getString(key, null)
        if (!choose && saved != null) {
            try { startActivity(Intent(intent).setPackage(saved)); return }
            catch (_: Exception) { prefs.edit().remove(key).apply() }
        }
        // Výběr aplikace uvnitř Průzkumníku umožňuje volbu skutečně uložit.
        val handlers = packageManager.queryIntentActivities(intent, PackageManager.MATCH_DEFAULT_ONLY)
            .distinctBy { it.activityInfo.packageName }
            .sortedBy { it.loadLabel(packageManager).toString().lowercase(Locale.ROOT) }
        if (handlers.isEmpty()) {
            try { startActivity(intent) } catch (_: Exception) { message(translated("No viewer available for this file type", "Pro tento typ souboru není dostupný prohlížeč", "No viewer available for this file type")) }
            return
        }
        if (!choose && handlers.size == 1) {
            try {
                startActivity(Intent(intent).setPackage(handlers[0].activityInfo.packageName))
                return
            } catch (_: Exception) { message(translated("Cannot open file", "Soubor nelze otevřít", "Cannot open file")) }
        }
        val labels = handlers.map { it.loadLabel(packageManager).toString() }.toTypedArray()
        AlertDialog.Builder(this).setTitle(translated("Open with – ${item.name}", "Otevřít pomocí – ${item.name}", "Open with – ${item.name}"))
            .setItems(labels) { _, index ->
                val pkg = handlers[index].activityInfo.packageName
                try {
                    startActivity(Intent(intent).setPackage(pkg))
                    prefs.edit().putString(key, pkg).apply()
                } catch (_: Exception) { message(translated("Selected app could not open the file", "Vybraná aplikace soubor neotevřela", "Selected app could not open the file")) }
            }
            .setNegativeButton(translated("Cancel", "Zrušit", "Cancel"), null).show()
    }

    private fun mediaContextMenu(item: RecentPhoto, kind: String) {
        val options = arrayOf(translated("Open", "Otevřít", "Open"), translated("Open with… (change app)", "Otevřít pomocí… (změnit aplikaci)", "Open with… (change app)"), translated("Select / deselect", "Označit / zrušit označení", "Select / deselect"),
            translated("Select all", "Vybrat vše", "Select all"), translated("Deselect all", "Zrušit výběr", "Deselect all"), translated("Copy", "Kopírovat", "Copy"), translated("Cut / move to…", "Vyjmout / přesunout do…", "Cut / move to…"),
            translated("Copy to…", "Kopírovat do…", "Copy to…"), translated("Share", "Sdílet", "Share"), translated("Rename", "Přejmenovat", "Rename"), translated("Delete", "Smazat", "Löschen"), translated("Add to favorites", "Přidat do oblíbených", "Add to favorites"), translated("Details", "Podrobnosti", "Details"))
        AlertDialog.Builder(this).setTitle(item.name).setItems(options) { _, choice ->
            when (choice) {
                0 -> openMedia(item, kind)
                1 -> openMedia(item, kind, true)
                2 -> { if (!selectedMedia.add(item.uri)) selectedMedia.remove(item.uri); showMediaGallery(kind) }
                3 -> { selectedMedia.clear(); selectedMedia.addAll(mediaItems.map { it.uri }); showMediaGallery(kind) }
                4 -> { selectedMedia.clear(); showMediaGallery(kind) }
                5, 6, 7 -> {
                    val items = mediaItems.filter { it.uri in selectedMedia }.ifEmpty { listOf(item) }
                    // Pro bezpečné kopírování používáme existující schránku aplikace.
                    if (choice == 6) {
                        message(translated("Moving requires selecting a destination folder; copying is available for now", "Přesun vyžaduje výběr cílové složky; zatím lze bezpečně kopírovat", "Moving requires selecting a destination folder; copying is available for now"))
                    } else {
                        photoClipboard = items
                        selectedMedia.clear()
                        phoneDir = Environment.getExternalStorageDirectory()
                        openPhone()
                        message(translated("Open destination folder and choose Paste selected files here", "Otevři cílovou složku a zvol Vložit vybrané soubory sem", "Open destination folder and choose Paste selected files here"))
                    }
                }
                8 -> try {
                    startActivity(Intent.createChooser(Intent(Intent.ACTION_SEND).apply {
                        type = mediaMime(item, kind)
                        putExtra(Intent.EXTRA_STREAM, viewUri(item))
                        addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                    }, translated("Share file", "Sdílet soubor", "Share file")))
                } catch (_: Exception) { message(translated("Sharing unavailable", "Sdílení není dostupné", "Sharing unavailable")) }
                9 -> {
                    val path = if (item.uri.scheme == "file") item.uri.path else null
                    if (path == null || !hasFullAccess()) message(translated("Renaming this file is unavailable", "Přejmenování tohoto souboru není dostupné", "Renaming this file is unavailable"))
                    else ask(translated("New name", "Nový název", "New name"), item.name) { name ->
                        val old = File(path)
                        if (!safeName(name) || !old.renameTo(File(old.parentFile, name))) message(translated("Rename failed", "Přejmenování se nezdařilo", "Rename failed"))
                        showMediaGallery(kind)
                    }
                }
                10 -> confirm("Opravdu smazat ${item.name}?") {
                    val path = if (item.uri.scheme == "file") item.uri.path else null
                    val success = try {
                        if (path != null && hasFullAccess()) File(path).delete()
                        else contentResolver.delete(item.uri, null, null) > 0
                    } catch (_: Exception) { false }
                    if (!success) message(translated("Deletion not permitted. Try opening the file in phone storage.", "Smazání není povoleno. Zkus soubor otevřít ve složce telefonu.", "Deletion not permitted. Try opening the file in phone storage."))
                    selectedMedia.remove(item.uri)
                    showMediaGallery(kind)
                }
                11 -> message(translated("File favorites will be added in a future version", "Oblíbené pro soubory doplníme v další verzi", "File favorites will be added in a future version"))
                12 -> AlertDialog.Builder(this).setTitle(translated("Details", "Podrobnosti", "Details"))
                    .setMessage(translated("Name", "Název", "Name") + ": ${item.name}\n" + translated("Type", "Typ", "Typ") + ": ${mediaMime(item, kind)}\n" + translated("Date", "Datum", "Datum") + ": ${SimpleDateFormat("dd.MM.yyyy HH:mm", Locale.getDefault()).format(Date(item.timestamp))}\nURI: ${item.uri}")
                    .setPositiveButton("OK", null).show()
            }
        }.show()
    }

    private var documentFilter = "all"
    private fun documentMatches(name: String): Boolean {
        val ext = name.substringAfterLast('.', "").lowercase(Locale.ROOT)
        return when (documentFilter) {
            "pdf" -> ext == "pdf"
            "word" -> ext in setOf("doc", "docx", "odt")
            "excel" -> ext in setOf("xls", "xlsx", "csv", "ods")
            "txt" -> ext in setOf("txt", "rtf")
            else -> true
        }
    }
    private fun showMediaGallery(kind: String) {
        mediaScreen = kind
        mode = "media_$kind"
        val title = when(kind) { "video" -> "Videa"; "audio" -> "Hudba"; else -> "Dokumenty" }
        screen(title)
        action(translated("← Home", "← Domů", "← Home")) { home() }
        val permission = when {
            Build.VERSION.SDK_INT < 33 -> Manifest.permission.READ_EXTERNAL_STORAGE
            kind == "video" -> Manifest.permission.READ_MEDIA_VIDEO
            kind == "audio" -> Manifest.permission.READ_MEDIA_AUDIO
            else -> null
        }
        if (permission != null && checkSelfPermission(permission) != PackageManager.PERMISSION_GRANTED && !hasFullAccess()) {
            text(translated("Allow storage access to view files.", "Pro zobrazení souborů povol přístup k úložišti.", "Allow storage access to view files."))
            action(translated("Allow access", "Povolit přístup", "Allow access")) { requestPermissions(arrayOf(permission), 202) }
            return
        }
        if (kind == "documents") {
            val filters = listOf("all", "pdf", "word", "excel", "txt")
            val labels = listOf(
                translated("All", "Vše", "Alle"), "PDF", "Word", "Excel", "TXT"
            )
            val bar = HorizontalScrollView(this).apply { isHorizontalScrollBarEnabled = false }
            val buttons = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
            filters.forEachIndexed { index, filter ->
                val chip = label(labels[index], 14, ink, filter == documentFilter).apply {
                    gravity = Gravity.CENTER; setPadding(dp(16), 0, dp(16), 0)
                    background = if (filter == documentFilter) solGradient(24) else shape(panel, 24)
                    setOnClickListener { documentFilter = filter; showMediaGallery("documents") }
                }
                buttons.addView(chip, LinearLayout.LayoutParams(-2, dp(40)).apply { marginEnd = dp(8) })
            }
            bar.addView(buttons)
            root.addView(bar, LinearLayout.LayoutParams(-1, dp(48)))
        }
        mediaItems = loadMedia(kind).let { items -> if (kind == "documents") items.filter { documentMatches(it.name) } else items }
        selectedMedia.retainAll(mediaItems.map { it.uri }.toSet())
        text(translated("${mediaItems.size} files • newest first", "${mediaItems.size} souborů • nejnovější nahoře", "${mediaItems.size} files • newest first"), 13)
        if (mediaItems.isEmpty()) {
            text(translated("No files available. Android restricts access to some private app files.", "Žádné dostupné soubory. Některé soukromé soubory aplikací Android nezpřístupní.", "No files available. Android restricts access to some private app files."))
            action(translated("↻ Refresh", "↻ Obnovit", "↻ Refresh")) { showMediaGallery(kind) }
            return
        }
        action(if (selectedMedia.size == mediaItems.size) translated("☐ Deselect all", "☐ Zrušit výběr", "☐ Deselect all") else translated("☑ Select all (${mediaItems.size})", "☑ Vybrat vše (${mediaItems.size})", "☑ Select all (${mediaItems.size})")) {
            if (selectedMedia.size == mediaItems.size) selectedMedia.clear()
            else { selectedMedia.clear(); selectedMedia.addAll(mediaItems.map { it.uri }) }
            showMediaGallery(kind)
        }
        if (selectedMedia.isNotEmpty()) {
            action(translated("📋 Copy selected (${selectedMedia.size}) to phone folder", "📋 Kopírovat vybrané (${selectedMedia.size}) do složky telefonu", "📋 Copy selected (${selectedMedia.size}) to phone folder")) {
                photoClipboard = mediaItems.filter { it.uri in selectedMedia }
                selectedMedia.clear()
                phoneDir = Environment.getExternalStorageDirectory()
                openPhone()
                message(translated("Open the destination folder and tap Paste selected files here", "Otevři cílovou složku a klepni na Vložit vybrané soubory sem", "Open destination folder and tap Paste selected files here"))
            }
        }
        action(translated("↻ Refresh", "↻ Obnovit", "↻ Refresh")) { showMediaGallery(kind) }
        val grid = GridView(this).apply {
            numColumns = if (kind == "video") 2 else 1
            horizontalSpacing = dp(7); verticalSpacing = dp(7)
            stretchMode = GridView.STRETCH_COLUMN_WIDTH
            selector = android.graphics.drawable.ColorDrawable(Color.TRANSPARENT)
            adapter = object : BaseAdapter() {
                override fun getCount() = mediaItems.size
                override fun getItem(position: Int): Any = mediaItems[position]
                override fun getItemId(position: Int) = position.toLong()
                override fun getView(position: Int, convertView: View?, parent: ViewGroup): View {
                    val item = mediaItems[position]
                    val video = kind == "video"
                    val row = LinearLayout(this@MainActivity).apply {
                        orientation = if (video) LinearLayout.VERTICAL else LinearLayout.HORIZONTAL
                        gravity = Gravity.CENTER_VERTICAL
                        setPadding(dp(8), dp(8), dp(8), dp(8))
                        background = shape(if (item.uri in selectedMedia) Color.rgb(47, 85, 127) else panel, 12)
                        setOnClickListener {
                            if (selectedMedia.isNotEmpty()) {
                                if (!selectedMedia.add(item.uri)) selectedMedia.remove(item.uri)
                                showMediaGallery(kind)
                            } else openMedia(item, kind)
                        }
                        setOnLongClickListener { mediaContextMenu(item, kind); true }
                    }
                    val icon = ImageView(this@MainActivity).apply {
                        setImageResource(when(kind) { "video" -> android.R.drawable.ic_media_play; "audio" -> android.R.drawable.ic_media_ff; else -> android.R.drawable.ic_menu_agenda })
                        tag = item.uri.toString()
                    }
                    row.addView(icon, LinearLayout.LayoutParams(if (video) -1 else dp(48), dp(if (video) 136 else 48)))
                    if (video) {
                        val key = item.uri.toString()
                        val cached = thumbCache.get(key)
                        if (cached != null) icon.setImageBitmap(cached)
                        else thumbnailPool.execute {
                            try {
                                val bitmap = contentResolver.loadThumbnail(item.uri, Size(240, 240), null)
                                thumbCache.put(key, bitmap)
                                runOnUiThread { if (icon.tag == key) icon.setImageBitmap(bitmap) }
                            } catch (_: Exception) { }
                        }
                        icon.scaleType = ImageView.ScaleType.CENTER_CROP
                    }
                    val details = LinearLayout(this@MainActivity).apply {
                        orientation = LinearLayout.HORIZONTAL; gravity = Gravity.CENTER_VERTICAL
                        setPadding(dp(8), dp(4), dp(4), dp(4))
                    }
                    val name = label(item.name + "\n" + SimpleDateFormat("dd.MM.yyyy HH:mm", Locale.getDefault()).format(Date(item.timestamp)), 12, ink)
                    details.addView(name, LinearLayout.LayoutParams(0, -2, 1f))
                    details.addView(label(if (item.uri in selectedMedia) "☑" else "☐", 21, accent))
                    row.addView(details, LinearLayout.LayoutParams(if (video) -1 else 0, -2, if (video) 0f else 1f))
                    return row
                }
            }
        }
        root.addView(grid, LinearLayout.LayoutParams(-1, 0, 1f))
    }

    private fun pasteRecentPhotos(directory: File) {
        if (transferBusy) { message(translated("Transfer already in progress", "Přenos již probíhá", "Transfer already in progress")); return }
        val photos = photoClipboard.toList()
        if (photos.isEmpty()) return
        transferBusy = true
        message(translated("Copying ${photos.size} photos…", "Kopíruji ${photos.size} fotografií…", "Copying ${photos.size} photos…"))
        io.execute {
            var copied = 0
            var skipped = 0
            photos.forEach { photo ->
                try {
                    val target = File(directory, photo.name)
                    if (!safeName(photo.name) || target.exists() || !target.canonicalPath.startsWith(directory.canonicalPath + File.separator)) {
                        skipped++
                    } else {
                        contentResolver.openInputStream(photo.uri)?.use { input ->
                            target.outputStream().use { output -> input.copyTo(output) }
                            copied++
                        } ?: run { skipped++ }
                    }
                } catch (_: Exception) { skipped++ }
            }
            runOnUiThread {
                transferBusy = false
                photoClipboard = emptyList()
                showPhone()
                message(translated("Copied: $copied, skipped: $skipped. Original photos remain on your phone.", "Zkopírováno: $copied, přeskočeno: $skipped. Původní fotky zůstaly v telefonu.", "Copied: $copied, skipped: $skipped. Original photos remain on your phone."))
            }
        }
    }

    private fun searchPhone(query: String) {
        if (!hasFullAccess()) { openPhone(); return }
        mode = "search"; screen(translated("Search", "Hledání", "Search"))
        text(translated("Results for: $query", "Výsledky pro: $query", "Results for: $query"))
        action(translated("← Back", "← Zpět", "← Back")) { home() }
        text(translated("Searching files…", "Prohledávám soubory…", "Searching files…"), 13)
        io.execute {
            val found = mutableListOf<File>()
            val stack = java.util.ArrayDeque<File>()
            stack.add(Environment.getExternalStorageDirectory())
            var visited = 0
            while (!stack.isEmpty() && visited < 12000 && found.size < 250) {
                val dir = stack.removeLast(); visited++
                val children = try { dir.listFiles() } catch (_: Exception) { null } ?: continue
                for (f in children) {
                    if (f.name.contains(query, true)) found.add(f)
                    if (f.isDirectory && !f.name.startsWith(".")) stack.add(f)
                }
            }
            runOnUiThread {
                if (mode != "search") return@runOnUiThread
                screen(translated("Search", "Hledání", "Search"))
                text(translated("$query • ${found.size} results", "$query • ${found.size} výsledků", "$query • ${found.size} results"))
                action(translated("← Back", "← Zpět", "← Back")) { home() }
                entries(found.map { f -> (if (f.isDirectory) "📁 " else "📄 ") + f.name to {
                    if (f.isDirectory) { phoneDir = f; showPhone() } else phoneMenu(f)
                } })
            }
        }
    }
    private fun hasFullAccess(): Boolean = Build.VERSION.SDK_INT >= 30 && Environment.isExternalStorageManager()
    private fun openPhone() {
        if (Build.VERSION.SDK_INT >= 30 && !hasFullAccess()) {
            AlertDialog.Builder(this).setTitle(translated("File access", "Přístup k souborům", "File access"))
                .setMessage(translated("File Explorer needs one-time All files access to display Downloads, Documents, photos and other common folders. Protected Android folders remain restricted.", "Průzkumník potřebuje jednorázově povolit Přístup ke všem souborům, aby mohl přímo zobrazovat Download, Documents, fotky a další běžné složky. Chráněné složky Androidu zůstávají omezené.", "File Explorer needs one-time All files access to display Downloads, Documents, photos and other common folders. Protected Android folders remain restricted."))
                .setPositiveButton(translated("Open settings", "Otevřít nastavení", "Open settings")) { _, _ ->
                    awaitingPermission = true
                    try { startActivity(Intent(Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION, Uri.parse("package:$packageName"))) }
                    catch (_: Exception) { startActivity(Intent(Settings.ACTION_MANAGE_ALL_FILES_ACCESS_PERMISSION)) }
                }.setNegativeButton(translated("Cancel", "Zrušit", "Cancel"), null).show()
        } else if (Build.VERSION.SDK_INT < 30) {
            // Pro starší Android použijeme systémový výběr složky.
            if (local != null) showLocal() else pickTree()
        } else showPhone()
    }
    override fun onResume() {
        super.onResume()
        if (awaitingPermission && hasFullAccess()) {
            awaitingPermission = false
            showPhone()
        } else if (mode == "phone" && hasFullAccess()) showPhone()
    }
    private fun showPhone() {
        if (!hasFullAccess()) { openPhone(); return }
        mode = "phone"
        if (!phoneDir.exists() || !phoneDir.isDirectory) phoneDir = Environment.getExternalStorageDirectory()
        val dir = phoneDir
        screen(if (selectionMode) translated("Selected: ${selectedFiles.size}", "Vybráno: ${selectedFiles.size}", "Selected: ${selectedFiles.size}") else "📁 " + (if (dir == Environment.getExternalStorageDirectory()) translated("Phone", "Telefon", "Phone") else dir.name))
        text(dir.absolutePath, 12)
        val bar = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
        val controls: List<Pair<String, () -> Unit>> = if (selectionMode) listOf(
            translated("Cancel", "Zrušit", "Cancel") to { selectedFiles.clear(); selectionMode = false; showPhone() },
            translated("Select all", "Vybrat vše", "Select all") to { selectedFiles.clear(); selectedFiles.addAll(dir.listFiles() ?: emptyArray()); showPhone() },
            translated("Copy", "Kopírovat", "Copy") to { saveClipboard(false) },
            translated("Cut", "Vyjmout", "Ausschneiden") to { saveClipboard(true) }
        ) else listOf(
            translated("⌂ Home", "⌂ Domů", "⌂ Home") to { home() },
            translated("↑ Back", "↑ Zpět", "↑ Back") to {
                val base = Environment.getExternalStorageDirectory()
                phoneDir = if (dir == base) base else dir.parentFile?.takeIf { it.absolutePath.startsWith(base.absolutePath) } ?: base
                showPhone()
            },
            translated("＋ Folder", "＋ Složka", "＋ Folder") to { ask(translated("New folder name", "Název nové složky", "New folder name")) { name ->
                if (!safeName(name) || !File(dir, name).mkdir()) message(translated("Cannot create folder", "Složku nelze vytvořit", "Cannot create folder")) else showPhone()
            } },
            translated("⋮ More", "⋮ Více", "⋮ More") to { AlertDialog.Builder(this).setItems(arrayOf(translated("Add file", "Přidat soubor", "Add file"), translated("Refresh", "Obnovit", "Refresh"), translated("Select files", "Označit soubory", "Select files"), translated("Select all in this folder", "Vybrat vše v této složce", "Select all in this folder"), translated("★ Add/remove current folder from favorites", "★ Přidat/odebrat složku z oblíbených", "★ Ordner als Favorit"))) { _, i ->
                when(i) {
                    0 -> { pendingPhoneDir = dir; pendingUploadLocal = false; chooseFile() }
                    1 -> showPhone()
                    2 -> { selectionMode = true; selectedFiles.clear(); showPhone() }
                    3 -> { selectionMode = true; selectedFiles.clear(); selectedFiles.addAll(dir.listFiles() ?: emptyArray()); showPhone() }
                    4 -> { setFavorite(dir); showPhone() }
                }
            }.show() }
        )
        controls.forEach { (caption, click) ->
            bar.addView(label(caption, 12, ink, true).apply {
                gravity = Gravity.CENTER; background = shape(panel, 11)
                setOnClickListener { click() }
            }, LinearLayout.LayoutParams(0, dp(46), 1f).apply { marginEnd = dp(5) })
        }
        root.addView(bar, LinearLayout.LayoutParams(-1, dp(46)).apply { bottomMargin = dp(10) })
        if (photoClipboard.isNotEmpty()) {
            action(translated("📸 Paste ${photoClipboard.size} photos here", "📸 Vložit ${photoClipboard.size} fotografií sem", "📸 Paste ${photoClipboard.size} photos here")) { pasteRecentPhotos(dir) }
            action(translated("✕ Clear photo selection", "✕ Zrušit výběr fotografií", "✕ Clear photo selection")) { photoClipboard = emptyList(); showPhone() }
        }
        if (clipboardFiles.isNotEmpty()) {
            action(translated("📋 Paste (${clipboardFiles.size}) here", "📋 Vložit (${clipboardFiles.size}) sem", "📋 Paste (${clipboardFiles.size}) here") + if (clipboardMove) translated(" • move", " • přesun", " • move") else translated(" • copy", " • kopie", " • Kopie")) { pasteClipboard(dir) }
            action(translated("✕ Clear clipboard", "✕ Vyprázdnit schránku", "✕ Clear clipboard")) { clipboardFiles = emptyList(); clipboardMove = false; showPhone() }
        }
        if (selectionMode && selectedFiles.isNotEmpty()) {
            action(translated("🗑 Delete selected (${selectedFiles.size})", "🗑 Smazat vybrané (${selectedFiles.size})", "🗑 Delete selected (${selectedFiles.size})")) {
                confirm(translated("Are you sure you want to delete ${selectedFiles.size} items? This cannot be undone.", "Opravdu smazat ${selectedFiles.size} položek? Tuto akci nelze vrátit.", "Are you sure you want to delete ${selectedFiles.size} items? This cannot be undone.")) {
                    val targets = selectedFiles.toList()
                    io.execute {
                        var errors = 0
                        targets.forEach { if (!deleteTree(it)) errors++ }
                        runOnUiThread { selectedFiles.clear(); selectionMode = false; showPhone(); message(if(errors == 0) translated("Deleted", "Smazáno", "Deleted") else translated("Some items could not be deleted: $errors", "Některé položky nešlo smazat: $errors", "Some items could not be deleted: $errors")) }
                    }
                }
            }
        }
        val files = try { dir.listFiles()?.sortedWith(compareBy<File> { !it.isDirectory }.thenBy { it.name.lowercase() }) ?: emptyList() }
                    catch (_: Exception) { emptyList() }
        if (files.isEmpty()) text(translated("Folder is empty or inaccessible.", "Složka je prázdná nebo nepřístupná.", "Folder is empty or inaccessible."), 14)
        entries(files.map { file ->
            (if (file.isDirectory) "📁 " else "📄 ") + (if (selectedFiles.contains(file)) "✓ " else "") + file.name to {
                if (selectionMode) {
                    if (!selectedFiles.add(file)) selectedFiles.remove(file)
                    showPhone()
                } else if (file.isDirectory) { phoneDir = file; showPhone() } else phoneMenu(file)
            }
        }, { index ->
            selectionMode = true
            selectedFiles.add(files[index]); showPhone()
        })
    }
    private fun saveClipboard(move: Boolean) {
        if (selectedFiles.isEmpty()) { message(translated("Select files first", "Nejdřív vyber soubory", "Select files first")); return }
        clipboardFiles = selectedFiles.toList()
        clipboardMove = move
        selectedFiles.clear(); selectionMode = false
        showPhone()
        message(translated("Clipboard contains: ${clipboardFiles.size} items. Open the destination folder and choose Paste.", "Ve schránce: ${clipboardFiles.size} položek. Otevři cílovou složku a zvol Vložit.", "Clipboard contains: ${clipboardFiles.size} items. Open the destination folder and choose Paste."))
    }
    private fun pasteClipboard(destination: File) {
        if (transferBusy || clipboardFiles.isEmpty()) return
        val sources = clipboardFiles.toList()
        val move = clipboardMove
        val conflicts = sources.filter { File(destination, it.name).exists() && it.canonicalPath != File(destination, it.name).canonicalPath }
        val proceed: () -> Unit = {
            transferBusy = true
            message(translated("Transferring ${sources.size} items…", "Probíhá přenos ${sources.size} položek…", "Transferring ${sources.size} items…"))
            io.execute {
                var success = 0
                val problems = mutableListOf<String>()
                for (source in sources) {
                    try {
                        if (!source.exists()) error(translated("Source no longer exists", "Zdroj už neexistuje", "Source no longer exists"))
                        val target = File(destination, source.name)
                        if (source.canonicalPath == target.canonicalPath) error(translated("Source and destination are the same", "Zdroj a cíl jsou stejné", "Source and destination are the same"))
                        if (source.isDirectory && destination.canonicalPath.startsWith(source.canonicalPath + File.separator)) error(translated("Cannot paste a folder into itself", "Nelze vložit složku do sebe", "Cannot paste a folder into itself"))
                        if (target.exists()) error(translated("Already exists at destination", "V cíli už existuje", "Already exists at destination"))
                        copyTree(source, target)
                        if (move && !deleteTree(source)) error(translated("Copied, but original could not be deleted", "Zkopírováno, ale původní položku nelze smazat", "Copied, but original could not be deleted"))
                        success++
                    } catch (e: Exception) { problems.add("${source.name}: ${e.message}") }
                }
                runOnUiThread {
                    transferBusy = false
                    if (problems.isEmpty()) { clipboardFiles = emptyList(); clipboardMove = false }
                    else { clipboardFiles = sources.filter { source -> problems.any { it.startsWith(source.name + ":") } } }
                    showPhone()
                    if (problems.isEmpty()) message(translated("Done: $success items", "Hotovo: $success položek", "Done: $success items"))
                    else AlertDialog.Builder(this).setTitle(translated("Transferred: $success / ${sources.size}", "Přeneseno: $success / ${sources.size}", "Transferred: $success / ${sources.size}"))
                        .setMessage(problems.take(12).joinToString("\n")).setPositiveButton("OK", null).show()
                }
            }
        }
        if (conflicts.isNotEmpty()) {
            AlertDialog.Builder(this).setTitle(translated("Duplicate names", "Shodné názvy", "Duplicate names"))
                .setMessage(translated("Already exists at destination ${conflicts.size} items with the same name. These items will be skipped; nothing will be overwritten.", "V cíli už existuje ${conflicts.size} položek se stejným názvem. Tyto položky přeskočíme; nic se nepřepíše.", "Already exists at destination ${conflicts.size} items with the same name. These items will be skipped; nothing will be overwritten."))
                .setPositiveButton(translated("Continue", "Pokračovat", "Continue")) { _, _ -> proceed() }.setNegativeButton(translated("Cancel", "Zrušit", "Cancel"), null).show()
        } else proceed()
    }
    private fun copyTree(source: File, target: File) {
        if (source.isDirectory) {
            if (!target.mkdir()) error(translated("Cannot create destination folder", "Nelze vytvořit cílovou složku", "Cannot create destination folder"))
            source.listFiles()?.forEach { child -> copyTree(child, File(target, child.name)) }
                ?: error(translated("Cannot read source folder", "Nelze přečíst zdrojovou složku", "Cannot read source folder"))
        } else {
            source.inputStream().use { input -> target.outputStream().use { output -> input.copyTo(output) } }
        }
    }
    private fun deleteTree(file: File): Boolean {
        if (file.isDirectory) {
            val children = file.listFiles() ?: return false
            if (children.any { !deleteTree(it) }) return false
        }
        return file.delete()
    }
    private fun safeName(name: String) = name.isNotBlank() && name != "." && name != ".." && !name.contains('/') && !name.contains('\\')
    private fun phoneMenu(file: File) {
        val actions = arrayOf(translated("Open", "Otevřít", "Open"), translated("Copy", "Kopírovat", "Copy"), translated("Cut", "Vyjmout", "Ausschneiden"), translated("Select multiple", "Označit více", "Select multiple"), translated("Rename", "Přejmenovat", "Rename"), translated("Delete", "Smazat", "Löschen"), translated("Copy to Windows", "Kopírovat do Windows", "Copy to Windows"), translated("★ Favorite folder", "★ Oblíbená složka", "★ Favoritenordner"))
        AlertDialog.Builder(this).setTitle(file.name).setItems(actions) { _, index ->
            when (index) {
                0 -> try {
                    val uri = FileProvider.getUriForFile(this, "$packageName.provider", file)
                    val ext = file.extension.lowercase()
                    val mime = MimeTypeMap.getSingleton().getMimeTypeFromExtension(ext) ?: "application/octet-stream"
                    startActivity(Intent.createChooser(Intent(Intent.ACTION_VIEW).apply {
                        setDataAndType(uri, mime); addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                    }, translated("Open soubor", "Otevřít soubor", "Open soubor")))
                } catch (e: Exception) { message(translated("Cannot open file: ${e.message}", "Soubor nelze otevřít: ${e.message}", "Cannot open file: ${e.message}")) }
                1 -> { selectedFiles.clear(); selectedFiles.add(file); saveClipboard(false) }
                2 -> { selectedFiles.clear(); selectedFiles.add(file); saveClipboard(true) }
                3 -> { selectionMode = true; selectedFiles.add(file); showPhone() }
                4 -> ask(translated("New name", "Nový název", "New name"), file.name) { name ->
                    if (!safeName(name) || !file.renameTo(File(file.parentFile, name))) message(translated("Rename failed", "Přejmenování se nepodařilo", "Rename failed"))
                    showPhone()
                }
                5 -> confirm("Opravdu smazat ${file.name}?") { if (!deleteTree(file)) message("Soubor nelze smazat"); showPhone() }
                7 -> setFavorite(if (file.isDirectory) file else file.parentFile ?: phoneDir)
                6 -> if (share == null) message(translated("Connect to Windows first", "Nejdřív se připoj k Windows", "Connect to Windows first")) else
                    ask(translated("SMB destination subfolder (for root enter \\\\)", "Cílová podsložka SMB (pro kořen napiš \\)", "SMB destination subfolder (for root enter \\\\)"), smbPath) { path ->
                        io.execute { try {
                            val target = join(path.trim('\\', '/'), file.name)
                            withSmb { smb -> smb.openFile(target, setOf(AccessMask.GENERIC_WRITE), null,
                                SMB2ShareAccess.ALL, SMB2CreateDisposition.FILE_OVERWRITE_IF,
                                setOf(SMB2CreateOptions.FILE_NON_DIRECTORY_FILE)).use { remote ->
                                file.inputStream().use { src -> remote.outputStream.use { src.copyTo(it) } }
                            } }
                            runOnUiThread { message(translated("Copied do Windows", "Zkopírováno do Windows", "Copied do Windows")) }
                        } catch (e: Exception) { runOnUiThread { message(translated("Copy error: ${e.message}", "Chyba kopírování: ${e.message}", "Copy error: ${e.message}")) } } }
                    }
            }
        }.show()
    }
    private fun pickTree() {
        startActivityForResult(Intent(Intent.ACTION_OPEN_DOCUMENT_TREE).apply {
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        }, folderRequest)
    }
    @Deprecated("Activity result API")
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (requestCode == zipSelectRequest) {
            if (resultCode == RESULT_OK && data != null) {
                val uris = mutableListOf<Uri>()
                data.data?.let { uris.add(it) }
                data.clipData?.let { clips -> for (i in 0 until clips.itemCount) uris.add(clips.getItemAt(i).uri) }
                zipSelectedUris = uris.distinct()
                if (zipSelectedUris.isNotEmpty()) startActivityForResult(Intent(Intent.ACTION_CREATE_DOCUMENT).apply {
                    type = "application/zip"; addCategory(Intent.CATEGORY_OPENABLE)
                    putExtra(Intent.EXTRA_TITLE, "Archive.zip")
                }, zipSaveRequest)
            }
            return
        }
        if (requestCode == zipSaveRequest) {
            if (resultCode == RESULT_OK && data?.data != null && zipSelectedUris.isNotEmpty()) createZip(data.data!!, zipSelectedUris)
            zipSelectedUris = emptyList()
            return
        }
        if (requestCode == zipOpenRequest) {
            if (resultCode == RESULT_OK && data?.data != null) {
                zipArchiveUri = data.data
                startActivityForResult(Intent(Intent.ACTION_OPEN_DOCUMENT_TREE).apply {
                    addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
                }, zipDestinationRequest)
            }
            return
        }
        if (requestCode == zipDestinationRequest) {
            val source = zipArchiveUri; zipArchiveUri = null
            if (resultCode == RESULT_OK && source != null && data?.data != null) extractZip(source, data.data!!)
            return
        }
        if (requestCode == scannerRequest) {
            if (resultCode == RESULT_OK) {
                val result = GmsDocumentScanningResult.fromActivityResultIntent(data)
                scannedPages = result?.pages?.map { it.imageUri } ?: emptyList()
                scannedPdf = result?.pdf?.uri
                scanSaveOptions()
            }
            return
        }
        if (requestCode == scanFolderRequest) {
            if (resultCode == RESULT_OK && data?.data != null) {
                val target = data.data!!
                try { contentResolver.takePersistableUriPermission(target,
                    Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION) }
                catch (_: Exception) { }
                saveScannedFiles(pendingScanName, target)
            }
            return
        }
        if (requestCode == scanCopyFolderRequest) {
            val pending = pendingScanCopy
            pendingScanCopy = null
            if (resultCode == RESULT_OK && data?.data != null && pending != null) {
                val folderUri = data.data!!
                io.execute {
                    try {
                        val folder = DocumentFile.fromTreeUri(this, folderUri) ?: error("Folder unavailable")
                        val mime = scanMime(pending.second)
                        val target = folder.createFile(mime, pending.second) ?: error("Cannot create file")
                        contentResolver.openInputStream(pending.first)!!.use { input ->
                            contentResolver.openOutputStream(target.uri, "w")!!.use { output -> input.copyTo(output) }
                        }
                        runOnUiThread { message(translated("Copy created", "Kopie vytvořena", "Kopie erstellt")); showScans() }
                    } catch (e: Exception) { runOnUiThread { message(translated("Copy failed: ${e.message}", "Kopírování selhalo: ${e.message}", "Kopieren fehlgeschlagen: ${e.message}")) } }
                }
            }
            return
        }
        if (requestCode == photoDeleteRequest) {
            if (pendingScanDeletion) {
                pendingScanDeletion = false
                if (resultCode == RESULT_OK) { selectedScans.clear(); message(translated("Scans deleted", "Skeny smazány", "Scans deleted")) }
                showScans(); return
            }
            if (resultCode == RESULT_OK) {
                selectedPhotos.removeAll(pendingPhotoDeletion.toSet())
                message(translated("Selected photos deleted", "Vybrané fotografie byly smazány", "Selected photos deleted"))
            } else message(translated("Photo deletion cancelled", "Mazání fotografií bylo zrušeno", "Photo deletion cancelled"))
            pendingPhotoDeletion = emptyList()
            if (mode == "screenshots") showScreenshots() else showPhotoGallery(photoScreen)
            return
        }
        if (resultCode != RESULT_OK) return
        val uri = data?.data ?: return
        when (requestCode) {
            folderRequest -> {
                try {
                    val flags = data.flags and (Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
                    contentResolver.takePersistableUriPermission(uri, flags)
                    localRoot = DocumentFile.fromTreeUri(this, uri); local = localRoot
                    getSharedPreferences("explorer", MODE_PRIVATE).edit().putString("tree", uri.toString()).apply()
                    showLocal()
                } catch (e: Exception) { message(translated("Cannot open folder: ${e.message}", "Nelze otevřít složku: ${e.message}", "Cannot open folder: ${e.message}")) }
            }
            uploadRequest -> {
                val phoneTarget = pendingPhoneDir
                if (phoneTarget != null) {
                    pendingPhoneDir = null
                    io.execute { try {
                        val name = queryDisplayName(uri) ?: "soubor"
                        if (!safeName(name)) error(translated("Invalid filename", "Neplatný název souboru", "Invalid filename"))
                        val dest = File(phoneTarget, name)
                        if (dest.exists()) error(translated("File already exists", "Soubor již existuje", "File already exists"))
                        contentResolver.openInputStream(uri)!!.use { input -> dest.outputStream().use { input.copyTo(it) } }
                        runOnUiThread { phoneDir = phoneTarget; showPhone(); message(translated("File added", "Soubor přidán", "File added")) }
                    } catch (e: Exception) { runOnUiThread { message("Chyba: ${e.message}") } } }
                } else if (pendingUploadLocal) {
                    val parent = local ?: return
                    io.execute { try {
                        val name = queryDisplayName(uri) ?: "soubor"
                        val dest = parent.createFile(contentResolver.getType(uri) ?: "application/octet-stream", name)
                            ?: error(translated("Cannot create file", "Nelze vytvořit soubor", "Cannot create file"))
                        contentResolver.openInputStream(uri)!!.use { src -> contentResolver.openOutputStream(dest.uri, "w")!!.use { src.copyTo(it) } }
                        runOnUiThread { showLocal(); message(translated("File copied", "Soubor zkopírován", "File copied")) }
                    } catch (e: Exception) { runOnUiThread { message("Chyba: ${e.message}") } } }
                } else {
                    val path = pendingUploadPath
                    io.execute { try {
                        val name = queryDisplayName(uri) ?: "soubor"
                        val remote = join(path, name)
                        withSmb { smb -> smb.openFile(remote, setOf(AccessMask.GENERIC_WRITE), null,
                            SMB2ShareAccess.ALL, SMB2CreateDisposition.FILE_OVERWRITE_IF,
                            setOf(SMB2CreateOptions.FILE_NON_DIRECTORY_FILE)).use { f ->
                            contentResolver.openInputStream(uri)!!.use { src -> f.outputStream.use { src.copyTo(it) } }
                        }
                        }
                        runOnUiThread { message(translated("Uploaded: $name", "Nahráno: $name", "Uploaded: $name")); showRemote() }
                    } catch (e: Exception) { runOnUiThread { message(translated("Upload failed: ${e.message}", "Nahrávání selhalo: ${e.message}", "Upload failed: ${e.message}")) } } }
                }
            }
            saveRequest -> {
                val path = pendingDownload ?: return
                io.execute { try {
                    withSmb { smb -> smb.openFile(path, setOf(AccessMask.GENERIC_READ), null,
                        SMB2ShareAccess.ALL, SMB2CreateDisposition.FILE_OPEN, null).use { remote ->
                        remote.inputStream.use { src -> contentResolver.openOutputStream(uri, "w")!!.use { src.copyTo(it) } }
                    } }
                    runOnUiThread { message(translated("Saved to phone", "Uloženo do telefonu", "Saved to phone")) }
                } catch (e: Exception) { runOnUiThread { message(translated("Download failed: ${e.message}", "Stahování selhalo: ${e.message}", "Download failed: ${e.message}")) } } }
            }
        }
    }
    private fun queryDisplayName(uri: Uri): String? = try {
        contentResolver.query(uri, arrayOf(android.provider.OpenableColumns.DISPLAY_NAME), null, null, null)?.use {
            if (it.moveToFirst()) it.getString(0) else null
        }
    } catch (_: Exception) { null }
    private fun showLocal() {
        mode = "local"
        val dir = local ?: return
        screen("📱 ${dir.name ?: "Telefon"}")
        action(translated("⌂ Home", "⌂ Domů", "⌂ Home")) { home() }
        action(translated("↑ Back", "↑ Zpět", "↑ Back")) { if (dir.uri == localRoot?.uri) home() else { local = dir.parentFile ?: localRoot; showLocal() } }
        action(translated("＋ New folder", "＋ Nová složka", "＋ New folder")) { ask(translated("Folder name", "Název složky", "Folder name")) { name ->
            if (dir.createDirectory(name) == null) message(translated("Cannot create folder", "Nelze vytvořit složku", "Cannot create folder")) else showLocal()
        } }
        action(translated("⬆ Add file to this folder", "⬆ Přidat soubor do této složky", "⬆ Add file to this folder")) { pendingUploadLocal = true; chooseFile() }
        val files = try { dir.listFiles().sortedWith(compareBy<DocumentFile> { !it.isDirectory }.thenBy { it.name?.lowercase() }) }
            catch (e: Exception) { message(e.message ?: translated("Read error", "Chyba čtení", "Read error")); emptyList() }
        entries(files.map { file ->
            (if (file.isDirectory) "📁 " else "📄 ") + (file.name ?: translated("Untitled", "Bez názvu", "Untitled")) to {
                if (file.isDirectory) { local = file; showLocal() } else localMenu(file)
            }
        })
    }
    private fun localMenu(file: DocumentFile) {
        val choices = arrayOf(translated("Open", "Otevřít", "Open"), translated("Rename", "Přejmenovat", "Rename"), translated("Delete", "Smazat", "Löschen"), translated("Copy to Windows", "Kopírovat do Windows", "Copy to Windows"))
        AlertDialog.Builder(this).setTitle(file.name).setItems(choices) { _, index ->
            when (index) {
                0 -> try {
                    val intent = Intent(Intent.ACTION_VIEW).apply {
                        setDataAndType(file.uri, file.type ?: "*/*"); addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                    }
                    startActivity(Intent.createChooser(intent, translated("Open", "Otevřít", "Open")))
                } catch (_: Exception) { message(translated("No app available to open file", "Chybí aplikace pro otevření souboru", "No app available to open file")) }
                1 -> ask(translated("New name", "Nový název", "New name"), file.name ?: "") { name -> if (!file.renameTo(name)) message(translated("Rename failed", "Přejmenování selhalo", "Rename failed")); showLocal() }
                2 -> confirm("Opravdu smazat ${file.name}?") { if (!file.delete()) message(translated("Deletion failed", "Smazání selhalo", "Deletion failed")); showLocal() }
                3 -> if (share == null) message(translated("Connect to Windows first", "Nejdřív se připoj k Windows", "Connect to Windows first")) else {
                    selectedLocal = file
                    ask(translated("Destination path on share $shareName (empty = root)", "Cílová cesta na disku $shareName (prázdné = kořen)", "Destination path on share $shareName (empty = root)"), smbPath) { path -> copyLocalToRemote(file, path) }
                    // Kořen lze zadat jako zpětné lomítko.
                }
            }
        }.show()
    }
    private fun copyLocalToRemote(file: DocumentFile, path: String) {
        io.execute { try {
            val target = join(path.trim('\\', '/'), file.name ?: "soubor")
            withSmb { smb -> smb.openFile(target, setOf(AccessMask.GENERIC_WRITE), null,
                SMB2ShareAccess.ALL, SMB2CreateDisposition.FILE_OVERWRITE_IF,
                setOf(SMB2CreateOptions.FILE_NON_DIRECTORY_FILE)).use { remote ->
                contentResolver.openInputStream(file.uri)!!.use { src -> remote.outputStream.use { src.copyTo(it) } }
            } }
            runOnUiThread { message(translated("Copied do Windows", "Zkopírováno do Windows", "Copied do Windows")) }
        } catch (e: Exception) { runOnUiThread { message(translated("Copy failed: ${e.message}", "Kopírování selhalo: ${e.message}", "Copy failed: ${e.message}")) } } }
    }
    private data class SavedSmb(val name: String, val host: String, val shareName: String,
                                val user: String, val domain: String)

    private fun savedSmb(): MutableList<SavedSmb> {
        val result = mutableListOf<SavedSmb>()
        val prefs = getSharedPreferences("explorer", MODE_PRIVATE)
        try {
            val array = JSONArray(prefs.getString("saved_smb", "[]"))
            for (i in 0 until array.length()) {
                val obj = array.getJSONObject(i)
                result.add(SavedSmb(obj.optString("name"), obj.optString("host"),
                    obj.optString("share"), obj.optString("user"), obj.optString("domain")))
            }
        } catch (_: Exception) { }
        // Jednorázově nabídneme dříve používané spojení i po aktualizaci aplikace.
        if (result.isEmpty() && !prefs.getBoolean("smb_migrated", false)) {
            val oldHost = prefs.getString("host", "") ?: ""
            val oldShare = prefs.getString("share", "") ?: ""
            if (oldHost.isNotBlank() && oldShare.isNotBlank()) {
                result.add(SavedSmb(oldHost, oldHost, oldShare,
                    prefs.getString("user", "") ?: "", ""))
                saveSmb(result)
            }
            prefs.edit().putBoolean("smb_migrated", true).apply()
        }
        return result
    }

    private fun saveSmb(items: List<SavedSmb>) {
        val array = JSONArray()
        items.forEach { item -> array.put(JSONObject().apply {
            put("name", item.name); put("host", item.host); put("share", item.shareName)
            put("user", item.user); put("domain", item.domain)
        }) }
        getSharedPreferences("explorer", MODE_PRIVATE).edit().putString("saved_smb", array.toString()).apply()
    }

    private fun smbConnections() {
        mode = "connect"
        screen(translated("🖥️ Network connections", "🖥️ Síťová připojení", "🖥️ Network connections"))
        action(translated("← Home", "← Domů", "← Home")) { home() }
        val saved = savedSmb()
        saved.forEach { item ->
            action(translated("💻 Connect to ${item.name}", "💻 Připojit na ${item.name}", "💻 Connect to ${item.name}")) { connectSavedSmb(item) }
            text("${item.host} / ${item.shareName}", 12)
            action("⋮ Upravit nebo odstranit: ${item.name}") {
                AlertDialog.Builder(this).setTitle(item.name)
                    .setItems(arrayOf("Upravit", "Odstranit")) { _, index ->
                        if (index == 0) connectionForm(item)
                        else confirm(translated("Remove saved connection ${item.name}?", "Odstranit uložené připojení ${item.name}?", "Remove saved connection ${item.name}?")) {
                            saveSmb(savedSmb().filterNot { it == item }); smbConnections()
                        }
                    }.show()
            }
        }
        action(translated("＋ New connection", "＋ Nové připojení", "＋ New connection")) { connectionForm() }
    }

    private fun connectSavedSmb(item: SavedSmb, password: String = "") {
        text(translated("Connecting to ${item.name}…", "Připojuji k ${item.name}…", "Connecting to ${item.name}…"), 13)
        io.execute {
            try {
                host = item.host; shareName = item.shareName; smbPath = ""
                smbUser = item.user; smbDomain = item.domain
                smbPassword.fill('\u0000'); smbPassword = password.toCharArray()
                reconnectSmb()
                runOnUiThread { showRemote() }
            } catch (e: Exception) {
                runOnUiThread {
                    message(translated("Connection failed: ${e.message}", "Připojení selhalo: ${e.message}", "Connection failed: ${e.message}"))
                    if (password.isEmpty() && item.user.isNotBlank() && !item.user.equals("guest", true)) {
                        val input = EditText(this).apply {
                            hint = translated("Password for ${item.user}", "Heslo pro ${item.user}", "Passwort für ${item.user}")
                            inputType = android.text.InputType.TYPE_CLASS_TEXT or
                                android.text.InputType.TYPE_TEXT_VARIATION_PASSWORD
                        }
                        AlertDialog.Builder(this).setTitle(translated("Password for ${item.name}", "Heslo k ${item.name}", "Passwort für ${item.name}")).setView(input)
                            .setPositiveButton(translated("Connect", "Připojit", "Verbinden")) { _, _ -> connectSavedSmb(item, input.text.toString()) }
                            .setNegativeButton(translated("Cancel", "Zrušit", "Cancel"), null).show()
                    }
                }
            }
        }
    }

    private fun connectionForm(edit: SavedSmb? = null) {
        mode = "connect"; screen(if (edit == null) translated("🖥️ New connection", "🖥️ Nové připojení", "🖥️ New connection") else translated("🖥️ Edit connection", "🖥️ Upravit připojení", "🖥️ Edit connection"))
        text(translated("SMB connection to a computer on the same network.", "Připojení SMB k počítači ve stejné síti.", "SMB connection to a computer on the same network."), 13)
        val displayName = field(translated("Connection name (e.g. My PC)", "Název připojení (např. Můj PC)", "Verbindungsname (z. B. Mein PC)"))
        val ip = field(translated("IP or computer name", "IP nebo název počítače", "IP or computer name"))
        val disk = field(translated("Shared folder name", "Název sdílené složky", "Shared folder name"))
        val user = field(translated("Windows username (Guest for guest access)", "Uživatel Windows (Guest pro hosta)", "Windows username (Guest for guest access)"))
        val pass = field(translated("Windows password", "Heslo Windows", "Windows-Passwort"), true)
        val domain = field(translated("Domain (optional)", "Doména (volitelné)", "Domain (optional)"))
        if (edit != null) {
            displayName.setText(edit.name); ip.setText(edit.host); disk.setText(edit.shareName)
            user.setText(edit.user); domain.setText(edit.domain)
        } else {
            val prefs = getSharedPreferences("explorer", MODE_PRIVATE)
            ip.setText(prefs.getString("host", "")); disk.setText(prefs.getString("share", ""))
            user.setText(prefs.getString("user", ""))
        }
        action(translated("Save and connect", "Uložit a připojit", "Save and connect")) {
            val h = ip.text.toString().trim(); val s = disk.text.toString().trim()
            val u = user.text.toString().trim(); val p = pass.text.toString(); val d = domain.text.toString().trim()
            val n = displayName.text.toString().trim().ifEmpty { h }
            if (h.isBlank() || s.isBlank()) { message(translated("Enter computer and share", "Vyplň počítač a sdílení", "Enter computer and share")); return@action }
            val item = SavedSmb(n, h, s, u, d)
            val list = savedSmb()
            if (edit != null) list.remove(edit)
            list.removeAll { it.name == n }
            list.add(item)
            saveSmb(list)
            getSharedPreferences("explorer", MODE_PRIVATE).edit()
                .putString("host", h).putString("share", s).putString("user", u).apply()
            // Hesla se z bezpečnostních důvodů neukládají do nešifrovaných předvoleb.
            connectSavedSmb(item, p)
        }
        action(translated("← Back to connections", "← Zpět na připojení", "← Back to connections")) { smbConnections() }
    }

    // 3.1: Přenos vybraných snímků přes stejné uložené SMB spojení jako v Síťová připojení.
    private fun sendRecentPhotosToSmb(target: SavedSmb, password: String = "") {
        val chosen = recentPhotos.filter { it.uri in selectedPhotos }
        if (chosen.isEmpty()) { message(translated("Select photos first", "Nejdřív vyber fotografie", "Select photos first")); return }
        confirm(translated("Send ${chosen.size} photos na ${target.name}?", "Odeslat ${chosen.size} fotografií na ${target.name}?", "Send ${chosen.size} photos na ${target.name}?")) {
            io.execute {
                try {
                    host = target.host; shareName = target.shareName; smbPath = ""
                    smbUser = target.user; smbDomain = target.domain
                    smbPassword.fill('\u0000'); smbPassword = password.toCharArray()
                    var uploaded = 0
                    for ((index, photo) in chosen.withIndex()) {
                        val name = photo.name.takeIf { safeName(it) }
                            ?: "fotografie_${System.currentTimeMillis()}_$index.jpg"
                        withSmb { disk ->
                            disk.openFile(name, setOf(AccessMask.GENERIC_WRITE), null,
                                SMB2ShareAccess.ALL, SMB2CreateDisposition.FILE_OVERWRITE_IF,
                                setOf(SMB2CreateOptions.FILE_NON_DIRECTORY_FILE)).use { remote ->
                                contentResolver.openInputStream(photo.uri)!!.use { input ->
                                    remote.outputStream.use { output -> input.copyTo(output) }
                                }
                            }
                        }
                        uploaded++
                    }
                    runOnUiThread { message(translated("To ${target.name} sent $uploaded photos", "Na ${target.name} odesláno $uploaded fotografií", "To ${target.name} sent $uploaded photos")) }
                } catch (e: Exception) {
                    runOnUiThread {
                        message(translated("Transfer to ${target.name} failed: ${e.message}", "Přenos na ${target.name} selhal: ${e.message}", "Transfer to ${target.name} failed: ${e.message}"))
                        if (password.isEmpty() && target.user.isNotBlank() &&
                            !target.user.equals("guest", true)) {
                            val field = EditText(this).apply {
                                hint = translated("Password for ${target.user}", "Heslo pro ${target.user}", "Passwort für ${target.user}")
                                inputType = android.text.InputType.TYPE_CLASS_TEXT or
                                    android.text.InputType.TYPE_TEXT_VARIATION_PASSWORD
                            }
                            AlertDialog.Builder(this).setTitle(translated("Sign in to ${target.name}", "Přihlášení k ${target.name}", "Sign in to ${target.name}"))
                                .setView(field)
                                .setPositiveButton("Zkusit znovu") { _, _ ->
                                    sendRecentPhotosToSmb(target, field.text.toString())
                                }.setNegativeButton(translated("Cancel", "Zrušit", "Cancel"), null).show()
                        }
                    }
                }
            }
        }
    }

    // Screenshoty jsou z MediaStore filtrovány podle složky, ne podle názvu souboru.
    private fun loadScreenshots(): List<RecentPhoto> {
        val result = mutableListOf<RecentPhoto>()
        val projection = arrayOf(MediaStore.Images.Media._ID, MediaStore.Images.Media.DISPLAY_NAME,
            MediaStore.Images.Media.RELATIVE_PATH, MediaStore.Images.Media.DATE_ADDED)
        try {
            contentResolver.query(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, projection, null,
                null, "${MediaStore.Images.Media.DATE_ADDED} DESC")?.use { c ->
                val id = c.getColumnIndexOrThrow(MediaStore.Images.Media._ID)
                val name = c.getColumnIndexOrThrow(MediaStore.Images.Media.DISPLAY_NAME)
                val path = c.getColumnIndexOrThrow(MediaStore.Images.Media.RELATIVE_PATH)
                val added = c.getColumnIndexOrThrow(MediaStore.Images.Media.DATE_ADDED)
                while (c.moveToNext()) {
                    val relative = c.getString(path) ?: ""
                    if (relative.split('/').any { it.equals("Screenshots", true) || it.equals("Screenshot", true) }) {
                        result.add(RecentPhoto(ContentUris.withAppendedId(
                            MediaStore.Images.Media.EXTERNAL_CONTENT_URI, c.getLong(id)),
                            c.getString(name) ?: "Screenshot", c.getLong(added) * 1000))
                    }
                }
            }
        } catch (e: Exception) { message(translated("Cannot load screenshots: ${e.message}", "Screenshoty nelze načíst: ${e.message}", "Cannot load screenshots: ${e.message}")) }
        return result
    }

    private fun showScreenshots() {
        mode = "screenshots"
        screen("Screenshoty")
        enableGalleryScrolling()
        action(translated("← Home", "← Domů", "← Home")) { home() }
        val permission = if (Build.VERSION.SDK_INT >= 33) Manifest.permission.READ_MEDIA_IMAGES
            else Manifest.permission.READ_EXTERNAL_STORAGE
        if (checkSelfPermission(permission) != PackageManager.PERMISSION_GRANTED && !hasFullAccess()) {
            text(translated("Allow image access", "Povol přístup k obrázkům", "Allow image access"))
            action(translated("Allow access", "Povolit přístup", "Allow access")) { requestPermissions(arrayOf(permission), 217) }
            return
        }
        recentPhotos = loadScreenshots()
        selectedPhotos.retainAll(recentPhotos.map { it.uri }.toSet())
        text(translated("Screenshots found: ${recentPhotos.size}", "Nalezeno screenshotů: ${recentPhotos.size}", "Screenshots found: ${recentPhotos.size}"))
        action(if (recentPhotos.isNotEmpty() && selectedPhotos.size == recentPhotos.size)
            translated("☐ Deselect all", "☐ Zrušit výběr", "☐ Deselect all") else translated("☑ Select all", "☑ Vybrat vše", "☑ Select all")) {
            if (selectedPhotos.size == recentPhotos.size) selectedPhotos.clear()
            else { selectedPhotos.clear(); selectedPhotos.addAll(recentPhotos.map { it.uri }) }
            showScreenshots()
        }
        if (selectedPhotos.isNotEmpty()) action(translated("🗑 Delete selected (${selectedPhotos.size})", "🗑 Smazat vybrané (${selectedPhotos.size})", "🗑 Delete selected (${selectedPhotos.size})")) {
            deleteSelectedScreenshots()
        }
        action(translated("↻ Refresh", "↻ Obnovit", "↻ Refresh")) { showScreenshots() }
        recentPhotos.forEach { item ->
            val row = LinearLayout(this).apply {
                gravity = Gravity.CENTER_VERTICAL
                background = shape(if (item.uri in selectedPhotos) Color.rgb(47, 85, 127) else panel, 12)
                setPadding(dp(8), dp(6), dp(8), dp(6))
            }
            val preview = ImageView(this).apply {
                scaleType = ImageView.ScaleType.CENTER_CROP
                try { setImageBitmap(contentResolver.loadThumbnail(item.uri, Size(100, 100), null)) }
                catch (_: Exception) { setImageResource(android.R.drawable.ic_menu_gallery) }
            }
            row.addView(preview, LinearLayout.LayoutParams(dp(68), dp(68)))
            row.addView(label("  ${if (item.uri in selectedPhotos) "☑" else "☐"}  ${item.name}", 14),
                LinearLayout.LayoutParams(0, -2, 1f))
            row.setOnClickListener {
                if (!selectedPhotos.add(item.uri)) selectedPhotos.remove(item.uri)
                showScreenshots()
            }
            root.addView(row, LinearLayout.LayoutParams(-1, -2).apply { bottomMargin = dp(7) })
        }
    }

    private fun deleteSelectedScreenshots() {
        val targets = recentPhotos.filter { it.uri in selectedPhotos }.map { it.uri }
        if (targets.isEmpty()) return
        confirm(translated("Permanently delete ${targets.size} screenshots?", "Opravdu trvale smazat ${targets.size} screenshotů?", "Permanently delete ${targets.size} screenshots?")) {
            if (Build.VERSION.SDK_INT >= 30) {
                try {
                    pendingPhotoDeletion = targets
                    val request = MediaStore.createDeleteRequest(contentResolver, targets)
                    startIntentSenderForResult(request.intentSender, photoDeleteRequest, null, 0, 0, 0)
                } catch (e: Exception) { message(translated("Deletion failed: ${e.message}", "Mazání selhalo: ${e.message}", "Deletion failed: ${e.message}")) }
            } else {
                targets.forEach { try { contentResolver.delete(it, null, null) } catch (_: Exception) {} }
                selectedPhotos.clear(); showScreenshots()
            }
        }
    }

    private fun startDocumentScanner() {
        val options = GmsDocumentScannerOptions.Builder()
            .setGalleryImportAllowed(true)
            .setPageLimit(30)
            .setResultFormats(GmsDocumentScannerOptions.RESULT_FORMAT_JPEG,
                GmsDocumentScannerOptions.RESULT_FORMAT_PDF)
            .setScannerMode(GmsDocumentScannerOptions.SCANNER_MODE_FULL)
            .build()
        GmsDocumentScanning.getClient(options).getStartScanIntent(this)
            .addOnSuccessListener { sender ->
                try { startIntentSenderForResult(sender, scannerRequest, null, 0, 0, 0) }
                catch (e: Exception) { message("Skener nelze spustit: ${e.message}") }
            }
            .addOnFailureListener { message(translated("Scanner unavailable: ${it.message}", "Skener není dostupný: ${it.message}", "Scanner unavailable: ${it.message}")) }
    }

    private fun scanSaveOptions() {
        if (scannedPages.isEmpty() && scannedPdf == null) return
        val options = arrayOf(translated("PDF – all pages", "PDF – všechny stránky", "PDF – all pages"), translated("JPG – individual pages", "JPG – jednotlivé stránky", "JPG – individual pages"))
        AlertDialog.Builder(this).setTitle(translated("Save scan as", "Uložit sken jako", "Save scan as"))
            .setItems(options) { _, i ->
                scanOutputFormat = if (i == 0) "pdf" else "jpg"
                val input = EditText(this).apply {
                    setSingleLine(true)
                    setText("Sken_${SimpleDateFormat("yyyy-MM-dd_HH-mm-ss", Locale.getDefault()).format(Date())}")
                    selectAll()
                }
                AlertDialog.Builder(this).setTitle(translated("Document name (without extension)", "Název dokumentu (bez přípony)", "Document name (without extension)"))
                    .setView(input)
                    .setPositiveButton(translated("Save to My scans", "Uložit do Moje skeny", "Save to My scans")) { _, _ ->
                        saveScannedFiles(input.text.toString(), null)
                    }
                    .setNeutralButton(translated("Choose another folder", "Vybrat jinou složku", "Choose another folder")) { _, _ ->
                        pendingScanName = input.text.toString()
                        startActivityForResult(Intent(Intent.ACTION_OPEN_DOCUMENT_TREE).apply {
                            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or
                                Intent.FLAG_GRANT_WRITE_URI_PERMISSION or
                                Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
                        }, scanFolderRequest)
                    }
                    .setNegativeButton(translated("Cancel", "Zrušit", "Cancel"), null).show()
            }.show()
    }

    private var pendingScanName = "Sken"
    private fun saveScannedFiles(rawName: String, folder: Uri?) {
        val name = rawName.trim().replace(Regex("[^\\p{L}\\p{N}_ -]"), "_").take(70)
            .ifBlank { "Sken" }
        val sources = if (scanOutputFormat == "pdf") listOfNotNull(scannedPdf) else scannedPages
        if (sources.isEmpty()) { message(translated("Scanner did not return requested format", "Skener nevrátil požadovaný formát", "Scanner did not return requested format")); return }
        io.execute {
            try {
                val targetFolder = folder?.let { DocumentFile.fromTreeUri(this, it) }
                val saved = mutableListOf<String>()
                sources.forEachIndexed { index, src ->
                    val extension = if (scanOutputFormat == "pdf") "pdf" else "jpg"
                    val filename = if (sources.size > 1) "${name}_${index + 1}.$extension" else "$name.$extension"
                    val mime = if (extension == "pdf") "application/pdf" else "image/jpeg"
                    val dest = if (targetFolder != null) {
                        targetFolder.createFile(mime, filename)?.uri ?: error(translated("Cannot create file", "Nelze vytvořit soubor", "Cannot create file"))
                    } else {
                        val values = ContentValues().apply {
                            put(MediaStore.MediaColumns.DISPLAY_NAME, filename)
                            put(MediaStore.MediaColumns.MIME_TYPE, mime)
                            put(MediaStore.MediaColumns.RELATIVE_PATH, "Documents/Skeny/")
                        }
                        contentResolver.insert(MediaStore.Files.getContentUri("external"), values)
                            ?: error("Cannot create scan")
                    }
                    contentResolver.openInputStream(src)!!.use { input ->
                        contentResolver.openOutputStream(dest, "w")!!.use { output -> input.copyTo(output) }
                    }
                    saved.add(filename)
                }
                runOnUiThread { message(translated("Saved: ${saved.joinToString()}", "Uloženo: ${saved.joinToString()}", "Gespeichert: ${saved.joinToString()}")); showScans() }
            } catch (e: Exception) { runOnUiThread { message(translated("Failed to save scan: ${e.message}", "Uložení skenu selhalo: ${e.message}", "Failed to save scan: ${e.message}")) } }
        }
    }

    private fun loadScans(): List<Pair<Uri, String>> {
        val found = mutableListOf<Pair<Uri, String>>()
        val cols = arrayOf(MediaStore.Files.FileColumns._ID, MediaStore.Files.FileColumns.DISPLAY_NAME,
            MediaStore.Files.FileColumns.RELATIVE_PATH)
        try {
            contentResolver.query(MediaStore.Files.getContentUri("external"), cols,
                "${MediaStore.Files.FileColumns.RELATIVE_PATH} LIKE ?",
                arrayOf("Documents/Skeny/%"), "${MediaStore.Files.FileColumns.DATE_ADDED} DESC")?.use { c ->
                val id = c.getColumnIndexOrThrow(MediaStore.Files.FileColumns._ID)
                val name = c.getColumnIndexOrThrow(MediaStore.Files.FileColumns.DISPLAY_NAME)
                while (c.moveToNext()) {
                    val n = c.getString(name) ?: continue
                    if (n.endsWith(".pdf", true) || n.endsWith(".jpg", true))
                        found.add(ContentUris.withAppendedId(MediaStore.Files.getContentUri("external"),
                            c.getLong(id)) to n)
                }
            }
        } catch (e: Exception) { message(translated("Cannot load scans: ${e.message}", "Skeny nelze načíst: ${e.message}", "Cannot load scans: ${e.message}")) }
        return found
    }

    private fun scanMime(name: String): String = if (name.endsWith(".pdf", true)) "application/pdf" else "image/jpeg"

    private fun openScan(uri: Uri, name: String, edit: Boolean = false) {
        val intent = Intent(if (edit) Intent.ACTION_EDIT else Intent.ACTION_VIEW).apply {
            setDataAndType(uri, scanMime(name))
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
            if (edit) addFlags(Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
            clipData = android.content.ClipData.newUri(contentResolver, name, uri)
        }
        try {
            startActivity(Intent.createChooser(intent, translated(
                if (edit) "Edit with…" else "Open with…",
                if (edit) "Upravit pomocí…" else "Otevřít pomocí…",
                if (edit) "Bearbeiten mit…" else "Öffnen mit…")))
        } catch (_: Exception) { message(translated("No compatible application installed", "Není nainstalovaná vhodná aplikace", "Keine passende App installiert")) }
    }

    private fun scanActions(uri: Uri, name: String) {
        val options = arrayOf(
            translated("Open", "Otevřít", "Öffnen"),
            translated("Open with…", "Otevřít v jiné aplikaci…", "Öffnen mit…"),
            translated("Edit with…", "Upravit v aplikaci…", "Bearbeiten mit…"),
            translated("Share / Send", "Sdílet / Odeslat", "Teilen / Senden"),
            translated("Copy to folder…", "Kopírovat do složky…", "In Ordner kopieren…"),
            translated("Rename", "Přejmenovat", "Umbenennen"),
            translated("Select / Deselect", "Označit / Zrušit výběr", "Auswählen / Abwählen"),
            translated("Details", "Podrobnosti", "Details"),
            translated("Delete", "Smazat", "Löschen"))
        AlertDialog.Builder(this).setTitle(name).setItems(options) { _, choice ->
            when (choice) {
                0, 1 -> openScan(uri, name)
                2 -> openScan(uri, name, true)
                3 -> { selectedScans.clear(); selectedScans.add(uri); shareScans() }
                4 -> {
                    pendingScanCopy = uri to name
                    startActivityForResult(Intent(Intent.ACTION_OPEN_DOCUMENT_TREE).apply {
                        addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
                    }, scanCopyFolderRequest)
                }
                5 -> {
                    val ext = name.substringAfterLast('.', "")
                    val base = if (ext.isNotEmpty()) name.dropLast(ext.length + 1) else name
                    ask(translated("New name", "Nový název", "Neuer Name"), base) { raw ->
                        val clean = raw.trim().replace(Regex("[/\\\\]"), "_")
                        val filename = if (ext.isNotEmpty()) "$clean.$ext" else clean
                        if (clean.isBlank()) { message(translated("Invalid name", "Neplatný název", "Ungültiger Name")) }
                        else try {
                            val values = ContentValues().apply { put(MediaStore.MediaColumns.DISPLAY_NAME, filename) }
                            if (contentResolver.update(uri, values, null, null) == 0) error("Rename not permitted")
                            showScans()
                        } catch (e: Exception) { message(translated("Rename failed: ${e.message}", "Přejmenování selhalo: ${e.message}", "Umbenennen fehlgeschlagen: ${e.message}")) }
                    }
                }
                6 -> { if (!selectedScans.add(uri)) selectedScans.remove(uri); showScans() }
                7 -> {
                    val size = try { contentResolver.openAssetFileDescriptor(uri, "r")?.use { it.length } ?: -1L } catch (_: Exception) { -1L }
                    AlertDialog.Builder(this).setTitle(name).setMessage("${scanMime(name)}\n${if (size >= 0) "$size bytes" else "Size unknown"}\n$uri")
                        .setPositiveButton("OK", null).show()
                }
                8 -> {
                    selectedScans.clear(); selectedScans.add(uri)
                    confirm(translated("Delete $name?", "Smazat $name?", "$name löschen?")) {
                        if (Build.VERSION.SDK_INT >= 30) try {
                            pendingScanDeletion = true
                            val req = MediaStore.createDeleteRequest(contentResolver, listOf(uri))
                            startIntentSenderForResult(req.intentSender, photoDeleteRequest, null, 0, 0, 0)
                        } catch (e: Exception) { message("${e.message}") }
                        else { try { contentResolver.delete(uri, null, null) } catch (_: Exception) {}; selectedScans.clear(); showScans() }
                    }
                }
            }
        }.show()
    }

    private fun showScans() {
        mode = "scans"; screen("Moje skeny"); enableGalleryScrolling()
        action(translated("← Home", "← Domů", "← Home")) { home() }
        scans = loadScans()
        selectedScans.retainAll(scans.map { it.first }.toSet())
        text(translated("Documents/Skeny • ${scans.size} documents", "Documents/Skeny • ${scans.size} dokumentů", "Documents/Skeny • ${scans.size} documents"), 13)
        action(translated("📄 New scan", "📄 Nový sken", "📄 New scan")) { startDocumentScanner() }
        action(if (scans.isNotEmpty() && selectedScans.size == scans.size)
            translated("☐ Deselect all", "☐ Zrušit výběr", "☐ Deselect all") else translated("☑ Select all", "☑ Vybrat vše", "☑ Select all")) {
            if (selectedScans.size == scans.size) selectedScans.clear()
            else { selectedScans.clear(); selectedScans.addAll(scans.map { it.first }) }
            showScans()
        }
        if (selectedScans.isNotEmpty()) {
            action(translated("↗ Share selected (${selectedScans.size})", "↗ Sdílet vybrané (${selectedScans.size})", "↗ Share selected (${selectedScans.size})")) { shareScans() }
            action(translated("🗑 Delete selected (${selectedScans.size})", "🗑 Smazat vybrané (${selectedScans.size})", "🗑 Delete selected (${selectedScans.size})")) {
                confirm(translated("Are you sure you want to delete ${selectedScans.size} scans?", "Opravdu smazat ${selectedScans.size} skenů?", "Are you sure you want to delete ${selectedScans.size} scans?")) {
                    val targets = selectedScans.toList()
                    if (Build.VERSION.SDK_INT >= 30) {
                        try {
                            pendingScanDeletion = true
                            val req = MediaStore.createDeleteRequest(contentResolver, targets)
                            startIntentSenderForResult(req.intentSender, photoDeleteRequest, null, 0, 0, 0)
                        } catch (e: Exception) { message(translated("Cannot delete: ${e.message}", "Nelze smazat: ${e.message}", "Löschen fehlgeschlagen: ${e.message}")) }
                    } else {
                        targets.forEach { try { contentResolver.delete(it, null, null) } catch (_: Exception) {} }
                        selectedScans.clear(); showScans()
                    }
                }
            }
        }
        scans.forEach { (uri, name) ->
            action("${if (uri in selectedScans) "☑  " else "📄  "}$name   ⋮") {
                scanActions(uri, name)
            }
        }
        action(translated("↻ Refresh", "↻ Obnovit", "↻ Refresh")) { showScans() }
    }

    private var pendingScanDeletion = false
    private fun shareScans() {
        val chosen = scans.filter { it.first in selectedScans }
        if (chosen.isEmpty()) return
        val uris = ArrayList(chosen.map { it.first })
        val type = if (chosen.all { it.second.endsWith(".pdf", true) }) "application/pdf"
            else if (chosen.all { it.second.endsWith(".jpg", true) }) "image/jpeg" else "*/*"
        val base = Intent(if (uris.size == 1) Intent.ACTION_SEND else Intent.ACTION_SEND_MULTIPLE).apply {
            this.type = type
            if (uris.size == 1) putExtra(Intent.EXTRA_STREAM, uris.first())
            else putParcelableArrayListExtra(Intent.EXTRA_STREAM, uris)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
            val clip = android.content.ClipData.newUri(contentResolver, "Skeny", uris.first())
            uris.drop(1).forEach { clip.addItem(android.content.ClipData.Item(it)) }
            clipData = clip
        }
        val apps = listOf("WhatsApp" to "com.whatsapp", "Messenger" to "com.facebook.orca",
            "Seznam Email" to "cz.seznam.email", "Gmail" to "com.google.android.gm",
            "Discord" to "com.discord")
        val buttons = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        val dialog = AlertDialog.Builder(this).setTitle(translated("Share scans", "Sdílet skeny", "Share scans")).setView(buttons)
            .setNegativeButton(translated("Cancel", "Zrušit", "Cancel"), null).create()
        apps.forEach { (title, pkg) ->
            val row = LinearLayout(this).apply { gravity = Gravity.CENTER_VERTICAL; setPadding(dp(16), dp(9), dp(12), dp(9)) }
            val iconView = ImageView(this).apply {
                try { setImageDrawable(packageManager.getApplicationIcon(pkg)) }
                catch (_: Exception) { setImageResource(android.R.drawable.ic_menu_share) }
            }
            row.addView(iconView, LinearLayout.LayoutParams(dp(38), dp(38)))
            row.addView(label("   $title", 16, Color.BLACK), LinearLayout.LayoutParams(-1, dp(45)))
            row.setOnClickListener {
                try { startActivity(Intent(base).setPackage(pkg)); dialog.dismiss() }
                catch (_: Exception) { message(translated("$title is unavailable or does not support this file", "$title není dostupný nebo nepodporuje tento soubor", "$title is unavailable or does not support this file")) }
            }
            buttons.addView(row)
        }
        val other = Button(this).apply { text = translated("More apps", "Další aplikace", "More apps"); setOnClickListener {
            try { startActivity(Intent.createChooser(base, translated("Share scans", "Sdílet skeny", "Share scans"))); dialog.dismiss() }
            catch (e: Exception) { message(translated("Sharing unavailable: ${e.message}", "Sdílení není dostupné: ${e.message}", "Sharing unavailable: ${e.message}")) }
        } }
        buttons.addView(other)
        dialog.show()
    }

    private fun join(path: String, name: String): String = if (path.isBlank()) name else "$path\\$name"
    private fun showRemote() {
        mode = "remote"; val current = smbPath
        screen("🖥️ $host / $shareName / $current")
        action(translated("⌂ Home", "⌂ Domů", "⌂ Home")) { home() }
        action(translated("↑ Back", "↑ Zpět", "↑ Back")) { smbPath = current.substringBeforeLast('\\', ""); showRemote() }
        action(translated("＋ New folder", "＋ Nová složka", "＋ New folder")) { ask(translated("Folder name", "Název složky", "Folder name")) { name ->
            io.execute { try { withSmb { it.mkdir(join(current, name)) }; runOnUiThread { showRemote() } }
                catch (e: Exception) { runOnUiThread { message("Chyba: ${e.message}") } } }
        } }
        action(translated("⬆ Upload file from phone", "⬆ Nahrát soubor z telefonu", "⬆ Upload file from phone")) { pendingUploadLocal = false; pendingUploadPath = current; chooseFile() }
        action(translated("🔄 Refresh", "🔄 Obnovit", "🔄 Refresh")) { showRemote() }
        text(translated("Loading files…", "Načítám soubory…", "Loading files…"), 13)
        io.execute { try {
            val found = withSmb { it.list(current) }.filter { it.fileName != "." && it.fileName != ".." }

            runOnUiThread {
                if (mode != "remote" || smbPath != current) return@runOnUiThread
                screen("🖥️ $host / $shareName / $current")
                action(translated("⌂ Home", "⌂ Domů", "⌂ Home")) { home() }
                action(translated("↑ Back", "↑ Zpět", "↑ Back")) { smbPath = current.substringBeforeLast('\\', ""); showRemote() }
                action(translated("＋ New folder", "＋ Nová složka", "＋ New folder")) { ask(translated("Folder name", "Název složky", "Folder name")) { name -> io.execute {
                    try { withSmb { it.mkdir(join(current, name)) }; runOnUiThread { showRemote() } }
                    catch (e: Exception) { runOnUiThread { message(e.message ?: "Chyba") } }
                } } }
                action(translated("⬆ Upload file from phone", "⬆ Nahrát soubor z telefonu", "⬆ Upload file from phone")) { pendingUploadLocal = false; pendingUploadPath = current; chooseFile() }
                action(translated("🔄 Refresh", "🔄 Obnovit", "🔄 Refresh")) { showRemote() }
                entries(found.map { item ->
                    val directory = (item.fileAttributes and 0x10L) != 0L
                    (if (directory) "📁 " else "📄 ") + item.fileName to {
                        val path = join(current, item.fileName)
                        if (directory) { smbPath = path; showRemote() } else remoteMenu(path, item.fileName)
                    }
                })
            }
        } catch (e: Exception) { runOnUiThread { message(translated("Cannot load: ${e.message}", "Nelze načíst: ${e.message}", "Cannot load: ${e.message}")) } } }
    }
    private fun remoteMenu(path: String, name: String) {
        AlertDialog.Builder(this).setTitle(name)
            .setItems(arrayOf(translated("Download to phone", "Stáhnout do telefonu", "Download to phone"), translated("Delete", "Smazat", "Löschen"))) { _, index ->
                when (index) {
                    0 -> { pendingDownload = path; startActivityForResult(Intent(Intent.ACTION_CREATE_DOCUMENT).apply {
                        type = "application/octet-stream"; addCategory(Intent.CATEGORY_OPENABLE)
                        putExtra(Intent.EXTRA_TITLE, name)
                    }, saveRequest) }
                    1 -> confirm("Opravdu smazat $name?") { io.execute { try {
                        withSmb { it.rm(path) }; runOnUiThread { showRemote() }
                    } catch (e: Exception) { runOnUiThread { message("Chyba: ${e.message}") } } } }
                }
            }.show()
    }
    private fun chooseFile() {
        startActivityForResult(Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
            type = "*/*"; addCategory(Intent.CATEGORY_OPENABLE)
            addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
        }, uploadRequest)
    }
    override fun onDestroy() {
        io.execute { closeSmbQuietly(); smbPassword.fill('\u0000') }
        thumbnailPool.shutdownNow()
        io.shutdown(); super.onDestroy()
    }
}
