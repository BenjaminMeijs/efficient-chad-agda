.PHONY: check html-render

check:
	agda --safe --without-K ./cost/chad-cost.agda
	agda --without-K ./correctness/chad-equiv-dsem.agda

html-render:
	agda --html --safe spec.agda
	sed -n '/elided in the paper appendix/ { p; : loop; n; /^<\/pre>/ b rest; b loop; }; : rest; p' html/spec.LACM.html >html/spec.LACM.trimmed.html
