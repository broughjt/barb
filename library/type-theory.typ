#let ofType = math.class("relation", $med :$)

#let piType(..arguments) = {
    let inputs = arguments.pos()
    let type = inputs.last()
    let variables = inputs.slice(0, -1).join($, $)

    $product_((#variables med : #type))$
}

#let sumType(..arguments) = {
    let inputs = arguments.pos()
    let type = inputs.last()
    let variables = inputs.slice(0, -1).join($, $)

    $sum_((#variables med : #type))$
}
