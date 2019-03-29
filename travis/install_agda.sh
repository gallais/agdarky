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
wget https://github.com/agda/agda-stdlib/archive/v0.17.tar.gz
tar -xvzf v0.17.tar.gz
# install agdarsec
wget https://github.com/gallais/agdarsec/archive/v0.3.0.tar.gz
tar -xvzf v0.3.0.tar.gz
# install generic-syntax
wget https://github.com/gallais/generic-syntax/archive/v0.2.tar.gz
tar -xvzf v0.2.tar.gz
