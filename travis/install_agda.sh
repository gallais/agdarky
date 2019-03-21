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
git checkout all-self
cd ..
# install generic-syntax
git clone https://github.com/gallais/generic-syntax
cd generic-syntax
git checkout 2a2dc29f7ef082a72e59e6be84db3c8e06cdc4e2
cd ..
# install agdarsec
git clone https://github.com/gallais/agdarsec
cd agdarsec
git checkout 9c3b216e84a36f551a8a6c496c4c2371a011a0c0
cd ..
