- no need for widening in finite domains

- intervalli con infinito diviso, altrimenti bisognava definire Z esteso a -inf e +inf

- A_sharp da definire ogni volta siccome dipende dagli abstract states

- between numero piu alto e numero piu basso sarebbe bot, ma e lasciato per semplicita

- abstract loop invariants based on narrowing not on widening


People usually say Coq does not allow writing non-terminating functions.

Coq cannot always know whether a program will terminate, because that would be a solution to the halting problem.

Coq is able to notice that a certain class of programs will terminate. The main heuristic it uses is that if one of the arguments to the function must get smaller on each recursive call, the program must terminate.

If you have a function that terminates, but Coq cannot tell that it terminates, you can add an extra argument that always get smaller on recursive calls. Doing this amounts to providing a proof that the function terminates.

So basically, Coq accepts any program that the user can prove the termination of.