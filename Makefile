agda_latex_dir = latex-agda
agda_files = main.lagda lib.lagda lc.lagda
agda_latex_files= $(agda_files:%.lagda=$(agda_latex_dir)/%.tex)

.PHONY: all agdatex

$(agda_latex_dir)/%.tex: %.lagda
	agda --latex --latex-dir=$(agda_latex_dir) $<

all: draft.pdf
agdatex: $(agda_latex_files)


draft.pdf: draft.lyx core.lyx common-preamble.tex $(agda_latex_files)
	lyx --export pdf2 draft.lyx
