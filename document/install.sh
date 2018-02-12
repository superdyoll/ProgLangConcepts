#!/bin/bash

function progress {
    echo "$(tput bold)$(tput setaf 4)==>$(tput sgr0) $(tput bold)$1$(tput sgr0)"
}

progress "Installing Pygments with the custom syntax highlighter..."
# Get the Pygments source through mercurial
hg clone https://bitbucket.org/birkenfeld/pygments-main
# Then inject our custom syntax highlighting
ln -s ../../../river_lexer.py pygments-main/pygments/lexers/river_lexer.py
# then Install Pygments
pip install -e pygments-main/.
# then update the list of lexers
cd pygments-main
make mapfiles
cd ..


progress "Installing LaTeX, (if you don't have it this will take ages!!)"
progress "this will fail if you don't have sudo!"
# Install xelatex (hopefully)
apt-get install texlive
