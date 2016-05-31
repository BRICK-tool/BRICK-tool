#!/bin/bash
echo "Building Checker~~~~~~~~~~~~~~~~~~~~~~~~"
cp mylib/lib* ../../../Release+Asserts/lib/
sudo cp mylib/lib* /usr/lib/
make
myPath="Bin"
if [ ! -d "$myPath" ]; then
	mkdir "$myPath"
fi 
sudo rm -r /usr/lib/buildCFG.so
sudo ln -s ../../../Release+Asserts/lib/buildCFG.so /usr/lib/buildCFG.so
g++ verify.cpp -o Bin/BRICK
sudo chmod -R 777 Bin
echo "Building finished!-----------------------Start run program in Directory Bin"

