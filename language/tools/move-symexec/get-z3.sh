#!/bin/bash -e

# Copyright (c) The Libra Core Contributors
# SPDX-License-Identifier: Apache-2.0

Z3_VERSION=4.8.9
if [[ "$(uname)" == "Darwin" ]]; then
  Z3_PLATFORM=x64-osx-10.14.6
elif [[ "$(uname)" == "Linux" ]]; then
  Z3_PLATFORM=x64-ubuntu-16.04
else
  echo "Platform not supported yet: (uname=$(uname))"
  return
fi

PKG=z3-${Z3_VERSION}-${Z3_PLATFORM}
DIR=$(dirname "$0")

mkdir -p ${DIR}/deps
pushd ${DIR}/deps

curl -LO https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${PKG}.zip
unzip ${PKG}.zip
mv ${PKG} z3
rm -rf ${PKG}.zip

popd
