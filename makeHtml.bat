mkdir output
cd output
del /q *
C:\metamath\metamath.exe "set scroll continuous" "read ..\linear.mm" "show statement * /html" "write theorem_list" "exit"
cd ..