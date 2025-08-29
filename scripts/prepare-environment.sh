#!/bin/bash

cd polyml
git am ../patches/polyml-fix-asm-elf-h.patch
if ! ./configure --bindir $(pwd) --with-gmp; then
  echo "Error: configuring polyml failed."
  exit 1
fi
if ! make -j $(nproc); then
  echo "Error: building polyml failed."
  exit 1
fi

cd ../HOL
find "help/Docfiles/HTML" -name "*.md.html" -delete
echo "val poly         = \"../polyml/poly\";"                > tools-poly/poly-includes.ML
echo "val polymllibdir = \"../polyml/libpolymain/.libs/\";" >> tools-poly/poly-includes.ML 

if ! ../polyml/poly < tools/smart-configure.sml; then
  echo "Error: smart-configuring HOL failed."
  exit 1
fi
if ! bin/build -j $(nproc); then
  echo "Error: building HOL failed."
  exit 1
fi

cd ../cakeml/pancake
if ! ../../HOL/bin/Holmake -j $(nproc); then
  echo "Error: Holmake of Pancake failed."
  exit 1
fi
cd semantics
if ! ../../../HOL/bin/Holmake -j $(nproc); then
  echo "Error: Holmake of Pancake semantics failed."
  exit 1
fi

cd ../../../z3
mkdir build
cd build
if ! cmake ..; then
  echo "Error: CMake for Z3 failed."
  exit 1
fi
if ! make -j $(nproc); then
  echo "Error: building Z3 failed."
  exit 1
fi
