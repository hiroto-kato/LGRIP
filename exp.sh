echo `date '+%y/%m/%d %H:%M:%S'`
cd src;
for f in ../test/*.mstrs;
do
    timeout 60 sml @SMLload=ind.x86-linux $f > ${f%%.*}.log;
done
echo `date '+%y/%m/%d %H:%M:%S'`

