#!/bin/bash

if ! command -v poly &> /dev/null; then
  echo "Error: 'poly' not found in PATH."
  exit 1
fi

cd HOL
if ! poly < tools/smart-configure.sml; then
  echo "Error: smart-configuring HOL failed."
  exit 1
fi

if ! bin/build; then
  echo "Error: building HOL failed."
  exit 1
fi

cd ../cakeml/pancake
if ! ../../HOL/bin/Holmake; then
  echo "Error: Holmake of Pancake failed."
  exit 1
fi

