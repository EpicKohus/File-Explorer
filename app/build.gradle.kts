plugins { id("com.android.application"); id("org.jetbrains.kotlin.android") }
android { namespace = "cz.fileexplorer"; compileSdk = 35
    defaultConfig { applicationId = "cz.fileexplorer.community"; minSdk = 26; targetSdk = 35; versionCode = 35; versionName = "3.5-community" }
    compileOptions { sourceCompatibility = JavaVersion.VERSION_17; targetCompatibility = JavaVersion.VERSION_17 }
    kotlinOptions { jvmTarget = "17" }
}
dependencies { implementation("com.google.zxing:core:3.5.3");  implementation("com.hierynomus:smbj:0.14.0"); implementation("androidx.documentfile:documentfile:1.0.1"); implementation("androidx.activity:activity-ktx:1.9.3"); implementation("com.google.android.gms:play-services-mlkit-document-scanner:16.0.0") }
