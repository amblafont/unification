agda_latex_dir = latex-agda
agda_files = Common.lagda lib.lagda lc.lagda main.lagda systemF.agda lcsig.lagda
agda_latex_files= $(agda_files:%.lagda=$(agda_latex_dir)/%.tex)
long_paper = paper-with-appendices
popl_paper = popl-paper


.PHONY: all agdatex popl

$(agda_latex_dir)/%.tex: %.lagda
	agda --latex --latex-dir=$(agda_latex_dir) $<

all: draft.pdf
agdatex: $(agda_latex_files)

draft.pdf: draft.lyx core.lyx jfp.layout common-preamble.tex ebutf8.sty $(agda_latex_files)
	lyx --export pdf2 draft.lyx

draft.tex: draft.lyx core.lyx common-preamble.tex ebutf8.sty $(agda_latex_files)
	lyx --export pdflatex draft.lyx -f all

$(long_paper).pdf: draft.pdf
	cp $< $@
#
$(popl_paper).pdf: draft.pdf
	pdftk $< cat 1-26 output $@

index.html: README.md
	pandoc -f markdown $< > $@
#
supplemental-material.zip: $(agda_files) index.html
# supplemental-material.zip: $(agda_files) README.md
	rm -f $@
	zip $@ $^


popl: $(popl_paper).pdf supplemental-material.zip

