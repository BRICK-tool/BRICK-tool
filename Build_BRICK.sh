#!/bin/bash
echo "Building Checker~~~~~~~~~~~~~~~~~~~~~~~~"
make
myPath="Bin"
LibDir="/usr/local/lib"
if [ ! -d "$myPath" ]; then
	mkdir "$myPath"
fi 
sudo rm -r {$LibDir}/buildCFG.so
sudo ln -s ../../../Release+Asserts/lib/buildCFG.so {$LibDir}/buildCFG.so
g++ main.cpp -o Bin/BRICK
sudo chmod -R 777 Bin
echo "Building finished!-----------------------Start run program in Directory Bin"

