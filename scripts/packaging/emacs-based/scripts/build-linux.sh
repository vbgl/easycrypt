#! /bin/bash

# --------------------------------------------------------------------
umask 077

# --------------------------------------------------------------------
function patchrpath {
  patchelf/src/patchelf --set-rpath '$ORIGIN:$ORIGIN/../lib' "${1}"
}

# --------------------------------------------------------------------
set -ex

# --------------------------------------------------------------------
[ ! -e _build ] || exit 1
mkdir _build && cd _build

# --------------------------------------------------------------------
# Install patchrpath

git clone --depth=1 https://github.com/NixOS/patchelf.git

( set -e; cd patchelf; autoreconf -i -f && ./configure && make )

# --------------------------------------------------------------------
# Build OPAM

export OPAMROOT="${PWD}/_opam"
export OPAMJOBS=${OPAMJOBS:-2}
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

patchrpath package/easycrypt/bin/easycrypt

# --------------------------------------------------------------------
mkdir -p package/easycrypt/{lib,share}/why3

cp -r _opam/system/lib/why3/plugins package/easycrypt/lib/why3/
cp -r _opam/system/lib/why3/why3-cpulimit package/easycrypt/bin/
cp -r _opam/system/share/why3 package/easycrypt/share/

# --------------------------------------------------------------------
for name in ${provers}; do
  cp _opam/system/bin/${name} package/easycrypt/bin/
  patchrpath package/easycrypt/bin/${name}
done

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
ldd package/easycrypt/bin/* | fgrep '=>' | \
    egrep -w 'libgmp|libpcre' | awk '{print $3}' | sort -u | \
    xargs -r -I '{}' -- cp '{}' package/easycrypt/lib/

# --------------------------------------------------------------------
BZIP2=-9 tar -C package --owner=0 --group=0 -cjf \
    "easycrypt-${ECNAME}.tbz2" easycrypt
