- check the division

- no need for widening in finite domains

- intervalli con infinito diviso, altrimenti bisognava definire Z esteso a -inf e +inf

- AI ha due argomenti aggiuntivi: numero di iterazioni nel loop, numero di iterazioni di widening. Vengono passati direttamente ad AI per motivi di controllo.

- A_sharp da definire ogni volta siccome dipende dagli abstract states

- Abstract states sono liste invece di funzioni per semplicita. Abstract states sono liste invece di option lists, per semplicità. Altrimenti molti pattern matching. Avrebbe senso assegnare None a bot state.

- between numero piu alto e numero piu basso sarebbe bot, ma e lasciato per semplicita
