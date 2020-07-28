# AFLplusplusSmart

## Description

This project integrates AFL++(2.63c/2.65c)  and aflsmart(5ad7ea3) in order to combine their parameters to improve fuzz efficiency.



## Usage

Same as [AFL++](https://github.com/AFLplusplus/AFLplusplus) [aflsmart](https://github.com/aflsmart/aflsmart)



## Parameters that may conflict

- libdislocator & aflsmart : Peach will get stuck when using libdislocator

If you find other conflicting parameters, please contact me :)



## About souce

master is 2.63c if you want to use 2.65c, just switch to the 2.65c branch. In branch 2.63c is the diff file of this project and AFL++2.63c

