(smod CLERKS is
  branches -> madrid ? vigo .
  employees(madrid) -> e(pepe, men) .
  employees(madrid) -> e(maria, men) .
  employees(vigo) -> e(pilar, women) ? e(luis, men) .
  search(e(N,S)) -> p(N,N) .
ends)

(eval-gen search(X) .)

eof

set print conceal off .
cont .
