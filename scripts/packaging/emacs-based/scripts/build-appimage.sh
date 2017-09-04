#! /bin/bash

# --------------------------------------------------------------------
umask 077

# --------------------------------------------------------------------
EMACS_U=https://github.com/probonopd/Emacs.AppImage/releases/download/AppImage/Emacs-25.1-glibc2.17-x86-64.AppImage
EMACS_L=Emacs-25.1-glibc2.17-x86-64.AppImage

# --------------------------------------------------------------------
set -ex

# --------------------------------------------------------------------
[ -e cache ] || mkdir cache

# --------------------------------------------------------------------
[   -e _build ] || exit 1
[   -e _build/package/easycrypt/__linux ] || exit 1
[ ! -e _build/appimage ] || exit 1

# --------------------------------------------------------------------
mkdir -p _build/appimage/EasyCrypt
cp -r _build/package/easycrypt/. _build/appimage/EasyCrypt
cp -r config/appimage/* _build/appimage/easycrypt/

# --------------------------------------------------------------------
if [ ! -e cache/${EMACS_L} ]; then
  wget -O cache/${EMACS_L} ${EMACS_U}
fi

cp cache/${EMACS_L} _build/appimage/EasyCrypt/bin/Emacs.AppImage
chmod +x _build/appimage/EasyCrypt/bin/Emacs.AppImage
chmod +x _build/appimage/EasyCrypt/AppRun
