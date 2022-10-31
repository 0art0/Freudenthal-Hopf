(TeX-add-style-hook
 "web"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("cleveref" "capitalize") ("blueprint" "showmore" "dep_graph" "coverage" "project=../../")))
   (TeX-run-style-hooks
    "latex2e"
    "macros_common"
    "macros_web"
    "content"
    "report"
    "rep10"
    "amsmath"
    "amsthm"
    "graphicx"
    "hyperref"
    "cleveref"
    "blueprint"
    "tikz-cd"
    "tikz"))
 :latex)

