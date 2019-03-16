#!/bin/sh
AGDA_VERSION=2.5.4.2

if ! type "agda" > /dev/null || [ ! `agda -V | sed "s/[^2]*//"` = "$AGDA_VERSION" ]; then
  cabal update
  cabal install alex happy cpphs --force-reinstalls
  cabal install Agda-"$AGDA_VERSION" --force-reinstalls
fi

mkdir -p $HOME/.agda
cp libraries-"$AGDA_VERSION" $HOME/.agda/
cd $HOME/.agda/
# install stdlib
git clone https://github.com/agda/agda-stdlib/ agda-stdlib-0.18
cd agda-stdlib-0.18
git checkout a0bfe7422d2aa0f0f49c9647659ce34e6e741375
cd ..
# install generic-syntax
git clone https://github.com/gallais/generic-syntax
cd generic-syntax
git checkout ac92fe766d396cd712538099e4fd12056f234b82
cd ..
# install agdarsec
git clone https://github.com/gallais/agdarsec
cd agdarsec
git checkout 71391d943d417805041e6c65e1ade32e97de6e08
cd ..
