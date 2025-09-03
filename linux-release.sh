#!/bin/bash

MAUDE_PATH=$HOME"/sistemas/Maude"
MAUDE_TAR="maude.tar.gz"
MAUDE_DIR="maude"

mkdir kkplural
cd kkplural
svn co svn+ssh://juanrh@gpd.sip.ucm.es/svn/plural/code
cd code/
chmod u+x put-together
./put-together 
cd ..
mkdir plural-maude-linux
cp code/plural.maude plural-maude-linux/
# cp ~/sistemas/Maude/maude-linux.tar.gz .
cp $MAUDE_PATH/$MAUDE_TAR .
# tar -xvzf maude-linux.tar.gz
tar -xvzf $MAUDE_TAR
#cp maude-linux/* plural-maude-linux/
cp $MAUDE_DIR/* plural-maude-linux/
echo ./maude.linux plural.maude > plural-maude-linux/plural.bin
chmod u+x plural-maude-linux/plural.bin
chmod u+x plural-maude-linux/maude.linux
tar -cvzf plural-maude-linux.tgz plural-maude-linux/
cp -f plural-maude-linux.tgz ..
cd ..
rm -rf kkplural
