LHSFILE=$(wildcard *.lagda)
TEXFILE=$(LHSFILE:.lagda=.tex)
PDF=$(TEXFILE:.tex=.pdf)
FMTS=$(wildcard *.fmt)

$(PDF): $(TEXFILE)
	rubber --pdf $<

$(TEXFILE): $(LHSFILE) $(FMTS) refs.bib
	lhs2TeX --agda -o $@ $<

clean:
	rubber --clean $(TEXFILE)
	rm -fv $(TEXFILE)

pdfshow: $(PDF)
	if [ -x /usr/bin/open ] ; then open $<; fi
	if [ -x /usr/bin/xpdf ] ; then xpdf $<; fi &


.PHONY: clean pdfshow
