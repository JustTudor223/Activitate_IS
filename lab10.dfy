method between (p: int, r: int) returns (q:int)
    requires r-p > 1
    ensures p < q < r
{
    q := p + 1;
}

/*
Descrierea funcționalității metodei between în Dafny: 
Aceasta metoda acceptă doi parametri întregi, p și r, și returnează un întreg q.
Funcția principală a acestei metode este de a seta q la p + 1 și apoi de a-l returna.

Precondiție detaliată: Metoda necesită ca diferența dintre r și p să fie mai mare de 1 (r - p > 1),
ceea ce este esențial pentru funcționarea corectă a metodei.

Postcondiție explicată: La finalul metodei, este garantat că valoarea lui q este mai mare decât p
și mai mică decât r (p < q < r). Această condiție verifică corectitudinea valorii returnate.

Impactul schimbării instrucțiunii în q := p + 2: Dacă instrucțiunea internă a metodei
este modificată astfel încât q este setat la p + 2, valoarea lui q se schimbă corespunzător.

Contraexemplu: Dacă p este 3 și r este 5, atribuirea inițială q := p + 1 ar rezulta în q = 4,
care îndeplinește postcondiția 3 < 4 < 5. Cu toate acestea, modificarea în q := p + 2 ar face ca
q să fie 5, ceea ce nu satisface postcondiția 3 < 5 < 5, demonstrând astfel că această modificare 
încalcă condițiile stabilite.
*/