#!/bin/bash -e

# Copyright (c) The Libra Core Contributors
# SPDX-License-Identifier: Apache-2.0

PKG=z3-4.8.9-x64-osx-10.14.6
DIR=$(dirname "$0")

pushd ${DIR}/deps

curl -LO https://github.com/Z3Prover/z3/releases/download/z3-4.8.9/${PKG}.zip
unzip ${PKG}.zip
mv ${PKG} z3
rm -rf ${PKG}.zip

popd
