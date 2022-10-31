(TeX-add-style-hook
 "print"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("report" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "textwidth=14cm") ("unicode-math" "warnings-off={mathtools-colon,mathtools-overbracket}") ("cleveref" "nameinlink" "capitalize")))
   (TeX-run-style-hooks
    "latex2e"
    "macros_common"
    "macros_print"
    "content"
    "report"
    "rep10"
    "geometry"
    "xfrac"
    "polyglossia"
    "amsmath"
    "enumitem"
    "tikz-cd"
    "unicode-math"
    "fontspec"
    "hyperref"
    "cleveref"
    "amsthm"
    "etexcmds"
    "thmtools"))
 :latex)

