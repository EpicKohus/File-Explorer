# File Explorer Community 3.3 – Android Studio source

## Implemented in this archive
- Separate app ID `cz.fileexplorer.community` and label `File Explorer Community`, installable alongside the Private app.
- Original Solana-themed folder icon, local file management, scanning, SMB, and scrolling home layout.
- Share selected images to WhatsApp, Messenger, Discord, Gmail or Android's system chooser. Recipients are chosen by the user.
- Personal quick shortcuts (Lukin, RMWORK, company server) are not included. The 10-minute photos shortcut is not offered; gallery defaults to all photos.
- Language setting: phone language / English / Czech / German. Main navigation, settings, and donation UI translated; many legacy file-management, scanner, SMB and gallery messages still need localization.
- Community-only Settings → Support development: Ko-fi https://ko-fi.com/pruzkumnik and a Solana (SOL) QR code + copyable public address. QR uses ZXing core.
- No donation buttons in the separate Private project.

## Important before distribution
1. Open the folder in Android Studio, sync dependencies, build and test on an Android device. **This project has not been compiled or device-tested here.**
2. Finish localization of remaining hard-coded Czech strings in the legacy screens.
3. Confirm your donation address, Ko-fi payment availability, and app-store policies. The external Ko-fi page may offer card / Google Pay depending on customer device and payment provider.
4. Review storage permission, privacy disclosures, security and SMB behavior. No hardcoded credentials or personal host addresses should be distributed.
5. Create and protect a release signing key and distribute a signed release, not an unverified debug build.
6. The original Private source has not been changed.
