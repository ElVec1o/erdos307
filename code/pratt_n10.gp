\\ pratt_n10.gp -- Pratt certificate data for lean/Erdos307/PrattN10.lean.
\\ Emits, bottom-up, each prime >= 1e9 needed by the N_10 inheritance result (prop:ppninherit),
\\ with a Lucas witness and the full factorisation of p - 1 (with multiplicity). Leaves below 1e9
\\ are left to norm_num. Run: gp -q code/pratt_n10.gp
LIM=10^9; done=Map(); out=List();
node(p)={
  my(f,L,a);
  if(p<LIM || mapisdefined(done,p), return);
  f=factor(p-1);
  for(i=1,#f~, node(f[i,1]));
  L=concat(vector(#f~,i,vector(f[i,2],j,f[i,1])));
  a=2; while(!(Mod(a,p)^(p-1)==1 && vecmin(apply(q->Mod(a,p)^((p-1)/q)!=1,f[,1]~))), a++);
  mapput(done,p,1); listput(out,[p,a,L]);
};
N9=5998279018951962402;
node(123572138719194583969192220095883252267503088389616114960309);
node(N9+1);
for(k=1,#out, print(out[k][1]," ",out[k][2]," ",out[k][3]));
quit;
