include agda_src.mk

LHSFILE=$(wildcard *.lagda)
TEXFILE=$(LHSFILE:.lagda=.tex)
PDF=$(TEXFILE:.tex=.pdf)
FMTS=$(wildcard *.fmt)

grayscale.pdf: $(PDF)
	gs -sOutputFile=grayscale.pdf -sDEVICE=pdfwrite \
		-sColorConversionStrategy=Gray -dProcessColorModel=/DeviceGray \
		-dCompatibilityLevel=1.4 -dNOPAUSE -dBATCH $(PDF)

$(PDF): $(TEXFILE)
	TEXMFOUTPUT=`pwd` rubber -v --pdf $<

$(TEXFILE): $(LHSFILE) $(FMTS) refs.bib
	lhs2TeX --agda -o $@ $<

extract: $(LHSFILE)
	lhs2TeX  --newcode $(LHSFILE) --agda  --no-pragmas > extracted/$(LHSFILE:.lagda=.agda)
	sed -i.bak s/doc\.ReflectionProofs/ReflectionProofs/g extracted/$(LHSFILE:.lagda=.agda)

check: extract
	agda $< --include-path=$(AGDA_SRC) --include-path=extracted --include-path=..

clean:
	rubber --clean $(TEXFILE)
	rm -fv $(TEXFILE)
	rm -v extracted/*

pdfshow: $(PDF)
	if [ -x /usr/bin/open ] ; then open $<; fi
	if [ -x /usr/bin/zathura ] ; then zathura $<; fi &

symbols:
	-rm -fv *.agdai # this is a terrible hack. module loading is broken :(
	cd .. ; agda --lagda doc/$(LHSFILE) --include-path=. --include-path=$(AGDA_SRC) > doc/generated-colour.fmt

.PHONY: clean pdfshow symbols $(PDF)
