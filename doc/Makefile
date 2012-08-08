include agda_src.mk

LHSFILE=$(wildcard *.lagda)
TEXFILE=$(LHSFILE:.lagda=.tex)
PDF=$(TEXFILE:.tex=.pdf)
FMTS=$(wildcard *.fmt)

$(PDF): $(TEXFILE)
	TEXMFOUTPUT=`pwd` rubber -v --pdf $<

$(TEXFILE): $(LHSFILE) $(FMTS) refs.bib
	lhs2TeX --agda -o $@ $<

extracted/ReflectionProofs.agda: $(LHSFILE)
	lhs2TeX  --newcode $(LHSFILE) --agda  --no-pragmas > $@

check: extracted/ReflectionProofs.agda
	agda $< --include-path=$(AGDA_SRC) --include-path=extracted

clean:
	rubber --clean $(TEXFILE)
	rm -fv $(TEXFILE)

pdfshow: $(PDF)
	if [ -x /usr/bin/open ] ; then open $<; fi
	if [ -x /usr/bin/xpdf ] ; then xpdf $<; fi &

symbols:
	-rm -fv *.agdai # this is a terrible hack. module loading is broken :(
	agda --lagda $(LHSFILE) --include-path=. --include-path=$(AGDA_SRC) > generated-colour.fmt

.PHONY: clean pdfshow symbols $(PDF)
