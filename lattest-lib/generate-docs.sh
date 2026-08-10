# remove any old docs
rm -r docs

# needed in case you have haddock turned on globally in Stack, e.g. for an IDE.
# In that case, without this purge, haddock refuses to generate docs because
# they already exist somewhere
stack purge

stack haddock --haddock-arguments '--hyperlinked-source --odir=docs'
