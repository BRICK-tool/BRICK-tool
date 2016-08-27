
BRICK: A BMC tool based on dReal


# How to Build
==================
## Binary Release
Please vist the [Binary at GitHub](https://github.com/BRICK-tool/BRICK_binary).
Use `./Build_BRICK.sh` before using the binary.

## Source Code and Build Instructions
You can download and build the source code of BRICK according to the following instructions:     
###Install g++-4.9
```
sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y    
sudo add-apt-repository ppa:dns/gnu -y     
sudo update-alternatives --remove-all gcc    
sudo update-alternatives --remove-all g++    
sudo apt-get update    
sudo apt-get install -qq g++-4.9     
sudo apt-get upgrade    
sudo apt-get dist-upgrade -y    
```
### Download LLVM and Clang
```
```
### Build and Install LLVM and Clang
```
cd llvm    
./configuration     
make     
sudo make install    
```
### Build and Install Minisat
```
git clone https://github.com/niklasso/minisat.git
cd minisat  
make
sudo make install     
```
### Build and Install Z3
```
git clone https://github.com/Z3Prover/z3.git
cd z3
python scripts/mk_make.py
cd build
make
sudo make install
```
### Build and Install dReal
```
git clone https://github.com/dreal/dreal3.git dreal
cd dreal
mkdir -p build/release
cd build/release
cmake -DCMAKE_BUILD_TYPE=RELEASE -DCMAKE_CXX_COMPILER=g++-4.9 -DCMAKE_C_COMPILER=gcc-4.9 -DBUILD_SHARED_LIB=ON ../../src
make
sudo make install
```
### Download and build BRICK
```
cd llvm/lib/Transforms    
git clone https://github.com/BRICK-tool/BRICK-tool.git    
cd BRICK-tool    
./Build_BRICK.sh    
```
The binary is in Directory Bin.     
Our tool is now mainly based on LLVM3.5. If there is any problem with other versions, please contact us.


#How to Use
==================
use Bin/BRICK to verify the functions

./BRICK < filename > -f < func > -b < bound > -p < precision > [-options].

 
