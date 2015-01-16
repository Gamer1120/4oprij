:: PLEASE MAKE A BACKUP OF THIS FILE BEFORE EDITING
@echo off
cd ..
cd bin
set /p name=Enter your name: 
java clientserver.ClientTUI %name%
pause