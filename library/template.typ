#import("mathyml/lib.typ") as mathyml
#import mathyml: to-mathml
#import mathyml.prelude: *

#import "type-theory.typ": *

#let template(body) = {
    show math.equation: to-mathml
    set raw(theme: none)
    show figure: it => {
        if target() == "html" { 
            html.elem("figure", attrs: (class: "typst"), html.frame(it))
        } else {
            it
        }
    }

    body
}
