(smod PARTY is

  call(enrique, drink) -> music .
  call(adri, meat) -> bread .
  call(rober, music) -> videogames .
  call(nacho, videogames) -> music .
  call(juan, food) -> drink .

  people -> enrique .
  people -> adri .
  people -> rober .
  people -> nacho .
  people -> juan .

  combine(bread, meat) -> burger .
  combine(burger, videogames) -> fun .

  makeCalls(P, S) -> S ? makeCalls(P, makeAnOffer(P, S)) .

  makeAnOffer(P, S) -> call(P, S) .
  makeAnOffer(P, S) -> combine(S, S) .

  haveFun(fun) -> tt .

  success(P, S) -> haveFun(makeCalls(P, S)) .
ends)

(path on .)

(width-first .)

(eval-gen success(P, S) .)

(show path .)

eof

(next .)

(show path .)