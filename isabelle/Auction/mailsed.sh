find -type f | while read i; do sed -i -e "s_ [^ ]*marco.caminati@gmail.com[^ ]*_ http://caminati.co.nr_g" $i; done
