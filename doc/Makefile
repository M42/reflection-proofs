AGDA_SRC=/home/paul/lib-0.6-agda/src


LHSFILE=$(wildcard *.lagda)
TEXFILE=$(LHSFILE:.lagda=.tex)
PDF=$(TEXFILE:.tex=.pdf)
FMTS=$(wildcard *.fmt)

$(PDF): $(TEXFILE)
	-rubber --pdf $<

$(TEXFILE): $(LHSFILE) $(FMTS) refs.bib
	-rm *.agdai -fv # this is a terrible hack. module loading is broken :(
	agda --lagda $(LHSFILE) --include-path=. --include-path=/home/paul/lib-0.6-agda/src > generated-colour.fmt
	lhs2TeX --agda -o $@ $<

extracted/ReflectionProofs.agda: $(LHSFILE)
	lhs2TeX  --newcode ReflectionProofs.lagda --agda  --no-pragmas > $@

check: extracted/ReflectionProofs.agda
	agda $< --include-path=$(AGDA_SRC) --include-path=extracted

clean:
	rubber --clean $(TEXFILE)
	rm -fv $(TEXFILE)

pdfshow: $(PDF)
	if [ -x /usr/bin/open ] ; then open $<; fi
	if [ -x /usr/bin/xpdf ] ; then xpdf $<; fi &


.PHONY: clean pdfshow
