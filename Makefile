agda_latex_dir = latex-agda
agda_files = Common.lagda lib.lagda lc.lagda main.lagda
agda_latex_files= $(agda_files:%.lagda=$(agda_latex_dir)/%.tex)

.PHONY: all agdatex

$(agda_latex_dir)/%.tex: %.lagda
	agda --latex --latex-dir=$(agda_latex_dir) $<

all: draft.pdf
agdatex: $(agda_latex_files)


draft.pdf: draft.lyx core.lyx common-preamble.tex ebutf8.sty $(agda_latex_files)
	lyx --export pdf2 draft.lyx
