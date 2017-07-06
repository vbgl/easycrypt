#! /bin/bash

# --------------------------------------------------------------------
umask 077

# --------------------------------------------------------------------
set -ex

# --------------------------------------------------------------------
[ ! -e _build ] || exit 1
mkdir _build && cd _build

# --------------------------------------------------------------------
# Build OPAM

export OPAMROOT="${PWD}/_opam"
export OPAMJOBS=2
export OPAMYES=true
export OCAMLBUILD_JOBS=${OPAMJOBS}
export ECNAME=${ECNAME:-$(date +'%d-%m-%Y')}

opam init -n
eval `opam config env`
opam repository add easycrypt git://github.com/EasyCrypt/opam.git
opam update

# --------------------------------------------------------------------
# Build EasyCrypt

git clone --depth=1 https://github.com/EasyCrypt/easycrypt.git

opam install --deps-only easycrypt
make -C easycrypt

# --------------------------------------------------------------------
# Build provers

provers="alt-ergo eprover z3"

opam install ${provers}

# --------------------------------------------------------------------
# Create package

mkdir -p package/easycrypt
mkdir -p package/easycrypt/etc
mkdir -p package/easycrypt/bin
mkdir -p package/easycrypt/lib
mkdir -p package/easycrypt/share

# --------------------------------------------------------------------
cp ../config/etc/* package/easycrypt/etc/

# --------------------------------------------------------------------
mkdir -p package/easycrypt/{lib,share}/easycrypt
mkdir -p package/easycrypt/share/

cp easycrypt/ec.native package/easycrypt/bin/easycrypt
cp easycrypt/system/callprover package/easycrypt/bin/
cp -r easycrypt/theories package/easycrypt/lib/easycrypt/

# --------------------------------------------------------------------
mkdir -p package/easycrypt/{lib,share}/why3

cp -r _opam/system/lib/why3/plugins package/easycrypt/lib/why3/
cp -r _opam/system/lib/why3/why3-cpulimit package/easycrypt/bin/
cp -r _opam/system/share/why3 package/easycrypt/share/

# --------------------------------------------------------------------
for name in ${provers}; do
  cp _opam/system/bin/${name} package/easycrypt/bin/
done

# --------------------------------------------------------------------
for name in easycrypt ${provers}; do
  dlls=$(otool -L package/easycrypt/bin/${name} \
    | fgrep .dylib | fgrep -v '@executable_path' \
    | egrep 'libgmp|libpcre' | awk '{print $1}')
  for dll in ${dlls}; do
    cp "${dll}" package/easycrypt/lib
    chmod +w "package/easycrypt/lib/$(basename ${dll})"
    install_name_tool -change \
      "${dll}" "@executable_path/../lib/$(basename ${dll})" \
      package/easycrypt/bin/${name}
  done
done

# --------------------------------------------------------------------
ECV=25.1

mkdir emacs && ( set -e; cd emacs; \
  curl -LO http://emacsformacosx.com/emacs-builds/Emacs-${ECV}-universal.dmg;
  7z x Emacs-${ECV}-universal.dmg || true;
  mv Emacs/Emacs.app ../package/easycrypt/share )

chmod +x package/easycrypt/share/Emacs.app/Contents/MacOS/Emacs*

# --------------------------------------------------------------------
mkdir pg && ( set -e; cd pg; \
  git clone --depth=1 https://github.com/ProofGeneral/PG.git; \
  rm -rf PG/.git && make -C PG clean )

mkdir -p package/easycrypt/share/easycrypt/pg
cp ../config/proofgeneral/emacs.rc package/easycrypt/share/easycrypt/pg/
mv pg/PG package/easycrypt/share/easycrypt/pg/ProofGeneral

# --------------------------------------------------------------------
cp ../config/scripts/run-easycrypt package/easycrypt/

# --------------------------------------------------------------------
BZIP2=-9 gtar -C package --owner=0 --group=0 -cjf \
    "easycrypt-${ECNAME}.tbz2" easycrypt
