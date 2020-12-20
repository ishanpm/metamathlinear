mkdir output
del /q output\*
xcopy html output /e/i
cd output
C:\metamath\metamath.exe "set scroll continuous" "read ..\linear.mm" "show statement * /alt_html" "write theorem_list" "exit"
cd ..
pause