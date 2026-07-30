read -p "Do you want to proceed with upload? (yes/no)" yn

case $yn in
    [Yy]* ) rsync -av src/symjit/ ../symjit/rust/; break;;
    * ) break;;
esac
