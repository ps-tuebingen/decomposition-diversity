#/bin/sh
sed -i.bak '1r additional_imports.txt' Names.hs
rm Names.hs.bak
