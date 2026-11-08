(function(){
'use strict';
var INF=Infinity,N_MIN=7,N_MAX=16,PM_DEF=30,PM_LIM=999;
var NS_SVG='http://www.w3.org/2000/svg';
var $=function(id){return document.getElementById(id);};
var clamp=function(v,a,b){return Math.max(a,Math.min(b,v));};
var letra=function(i){return String.fromCharCode(65+i);};
var tdist=function(x){return x===INF?'∞':String(x);};

/* ---------- estado ---------- */
var n=8,aristas=[],cols=[],nivelMax=1,modo='rand';
var src=0,dst=7;
var nodoSel=null,nodoSel2=null,ultimoPeso='1';
var pasos=[],paso=0;
var zoom=1,panX=0,panY=0,tocado=false;
var LW=700,LH=420;
var movNodos={},formaManual={},formaAuto={},posPeso={},tamPeso={},claveGuardada=null;
var Pauto={},Pbase={},etqBase={};
var gRoot=null,editor=null,editorK=-1,lastTap={k:-1,t:0};

var canvas=$('canvas'),svg=$('svg');

/* ---------- utilidades geométricas ---------- */
function radioNodo(){return n<=9?18:(n<=12?16:15);}
function bez(p0,c,p1,t){var a=(1-t)*(1-t),b=2*t*(1-t),d=t*t;return [a*p0[0]+b*c[0]+d*p1[0],a*p0[1]+b*c[1]+d*p1[1]];}
function formaDeControl(p0,p1,c){var dx=p1[0]-p0[0],dy=p1[1]-p0[1],L2=Math.max(dx*dx+dy*dy,1),qx=c[0]-p0[0],qy=c[1]-p0[1];return [(qx*dx+qy*dy)/L2,(-qx*dy+qy*dx)/L2];}
function controlDeForma(p0,p1,a,b){var dx=p1[0]-p0[0],dy=p1[1]-p0[1];return [p0[0]+a*dx-b*dy,p0[1]+a*dy+b*dx];}
function distSeg(p,a,b){
  var dx=b[0]-a[0],dy=b[1]-a[1],l2=dx*dx+dy*dy;
  if(l2===0)return Math.hypot(p[0]-a[0],p[1]-a[1]);
  var t=clamp(((p[0]-a[0])*dx+(p[1]-a[1])*dy)/l2,0,1);
  return Math.hypot(p[0]-(a[0]+t*dx),p[1]-(a[1]+t*dy));
}
function orient(p,q,r){return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0]);}
function seCruzan(a,b,c,d){return orient(a,b,c)*orient(a,b,d)<0&&orient(c,d,a)*orient(c,d,b)<0;}
function caja(pts){var x0=1e9,y0=1e9,x1=-1e9,y1=-1e9;for(var i=0;i<pts.length;i++){var p=pts[i];if(p[0]<x0)x0=p[0];if(p[0]>x1)x1=p[0];if(p[1]<y0)y0=p[1];if(p[1]>y1)y1=p[1];}return [x0,y0,x1,y1];}
function solapan(a,b){return !(a[2]<b[0]||b[2]<a[0]||a[3]<b[1]||b[3]<a[1]);}
function enCaja(x,y,r){return r[0]<=x&&x<=r[2]&&r[1]<=y&&y<=r[3];}

/* ---------- grafo ---------- */
function generarAleatorio(cant,pmax){
  var lista=[];
  for(var j=1;j<cant;j++){
    var a=Math.max(0,j-4);
    var k=a+Math.floor(Math.random()*(j-a));
    lista.push([k,j,1+Math.floor(Math.random()*pmax)]);
    for(var i=a;i<j;i++){
      if(i!==k&&Math.random()<0.35)lista.push([i,j,1+Math.floor(Math.random()*pmax)]);
    }
  }
  return lista;
}
function hayCamino(a,b){
  var vis=[a],pila=[a];
  while(pila.length){
    var x=pila.pop();
    if(x===b)return true;
    for(var i=0;i<aristas.length;i++){
      var e=aristas[i];
      if(e[0]===x&&vis.indexOf(e[1])<0){vis.push(e[1]);pila.push(e[1]);}
    }
  }
  return false;
}
function validarArista(u,v,w){
  if(u===v)return 'Una arista no puede unir un vértice consigo mismo.';
  if(!(w>0))return 'El peso debe ser un número positivo.';
  for(var i=0;i<aristas.length;i++)if(aristas[i][0]===u&&aristas[i][1]===v)return 'La arista '+letra(u)+'→'+letra(v)+' ya existe.';
  if(hayCamino(v,u))return 'No se añadió '+letra(u)+'→'+letra(v)+': formaría un ciclo y el grafo debe ser acíclico.';
  return '';
}

/* ---------- disposición por capas ---------- */
function calcularPosiciones(){
  cols=[];nivelMax=1;
  if(n===0)return;
  var i,k;
  if(modo==='man'){
    var o=src,d=dst,inter=[];
    for(i=0;i<n;i++)if(i!==o&&i!==d)inter.push(i);
    cols.push([o]);
    var chunk=Math.max(1,Math.ceil(inter.length/Math.max(1,n-3)));
    for(i=0;i<inter.length;i+=chunk)cols.push(inter.slice(i,i+chunk));
    if(d!==o)cols.push([d]);
    nivelMax=Math.max(1,cols.length-1);
    return;
  }
  if(!aristas.length){
    var todos=[];for(i=0;i<n;i++)todos.push(i);
    cols=[todos];nivelMax=1;return;
  }
  var nivel=[];for(i=0;i<n;i++)nivel.push(0);
  for(var rep=0;rep<n;rep++)for(k=0;k<aristas.length;k++){
    var a=aristas[k];
    if(nivel[a[0]]+1>nivel[a[1]])nivel[a[1]]=nivel[a[0]]+1;
  }
  var M=Math.max.apply(null,nivel);if(M<1)M=1;
  for(i=0;i<=M;i++)cols.push([]);
  for(i=0;i<n;i++)cols[nivel[i]].push(i);
  var pred=[],succ=[];
  for(i=0;i<n;i++){pred.push([]);succ.push([]);}
  aristas.forEach(function(e){pred[e[1]].push(e[0]);succ[e[0]].push(e[1]);});
  var rango={};
  function act(){cols.forEach(function(l){l.forEach(function(v,kk){rango[v]=(kk+1)/(l.length+1);});});}
  function ordenar(l,vec){
    var pares=cols[l].map(function(v,kk){
      var cl;
      if(vec[v].length){var s=0;vec[v].forEach(function(x){s+=rango[x];});cl=s/vec[v].length;}else cl=rango[v];
      return [cl,kk,v];
    });
    pares.sort(function(p,q){return p[0]-q[0]||p[1]-q[1]||p[2]-q[2];});
    cols[l]=pares.map(function(p){return p[2];});
  }
  act();
  for(var r=0;r<8;r++){
    for(var idx=1;idx<cols.length;idx++){ordenar(idx,pred);act();}
    for(idx=cols.length-2;idx>=0;idx--){ordenar(idx,succ);act();}
  }
  nivelMax=M;
}
function tamanoLogico(){
  var R=radioNodo(),maxcol=1;
  cols.forEach(function(l){if(l.length>maxcol)maxcol=l.length;});
  var cw=canvas.clientWidth||380,ch=canvas.clientHeight||340;
  LW=Math.max(cw,520,nivelMax*92+2*56+20);
  LH=Math.max(ch,380,maxcol*(2*R+34)+(R+38)+(R+30));
}
function posicionesPixel(W,H){
  var R=radioNodo(),izq=56,arriba=R+38,abajo=R+30;
  var ancho=W-2*izq,alto=H-arriba-abajo,P={};
  var paso=ancho/Math.max(1,nivelMax);
  var ys={};
  cols.forEach(function(l){l.forEach(function(v,k){ys[v]=(k+0.5)/l.length;});});
  var carriles=[0.5,0.12,0.88,0.31,0.69],cont=0;
  cols.forEach(function(l){
    if(l.length===1){ys[l[0]]=carriles[cont%carriles.length];cont++;}else cont=0;
  });
  var vals=Object.keys(ys).map(function(k){return ys[k];});
  var ymin=Math.min.apply(null,vals),ymax=Math.max.apply(null,vals);
  cols.forEach(function(l,li){
    l.forEach(function(i){
      var fy=(ymax-ymin<1e-9)?0.5:(ys[i]-ymin)/(ymax-ymin);
      P[i]=[izq+li*paso,arriba+fy*alto];
    });
  });
  return P;
}
function actualizarPosiciones(){
  Pauto=posicionesPixel(LW,LH);
  Pbase={};
  for(var i in Pauto){
    var m=movNodos[i]||[0,0];
    Pbase[i]=[Pauto[i][0]+m[0],Pauto[i][1]+m[1]];
  }
}

/* ---------- rutas de las aristas (curvas de Bézier) ---------- */
function calcularRutas(P){
  var R=radioNodo(),NS=14,nA=aristas.length,j,i,k;
  var orden=aristas.map(function(a,kk){return [Math.hypot(P[a[0]][0]-P[a[1]][0],P[a[0]][1]-P[a[1]][1]),kk];})
    .sort(function(a,b){return a[0]-b[0]||a[1]-b[1];}).map(function(p){return p[1];});
  var ctrls={},burdas={},cajas={},reservas=[];
  for(j in P){var x=P[j][0],y=P[j][1];reservas.push([x-44,y-R-21,x+44,y-R-3]);}
  orden.forEach(function(kk){
    var u=aristas[kk][0],v=aristas[kk][1],p0=P[u],p1=P[v];
    var mx=(p0[0]+p1[0])/2,my=(p0[1]+p1[1])/2,dx=p1[0]-p0[0],dy=p1[1]-p0[1];
    var ln=Math.max(Math.hypot(dx,dy),1),nx=-dy/ln,ny=dx/ln,mejor=null;
    var sep=nA<20?36:46,maxC=Math.min(360,100+nA*10),cand=[0];
    for(var nc=1;nc<=Math.floor(maxC/sep);nc++)cand.push(nc*sep,-nc*sep);
    cand.forEach(function(off){
      var ctrl=[mx+nx*2*off,my+ny*2*off],pts=[];
      for(var q=0;q<=NS;q++)pts.push(bez(p0,ctrl,p1,q/NS));
      var pen=Math.abs(off)*0.3;
      if(off===0&&nA>3)pen+=300;
      for(var jj in P){
        var jn=+jj;if(jn===u||jn===v)continue;
        var dmin=999999;
        for(var s=0;s<NS;s++){var dd=distSeg(P[jj],pts[s],pts[s+1]);if(dd<dmin)dmin=dd;}
        if(dmin<R+12)pen+=900+(R+12-dmin)*35;
      }
      pts.forEach(function(pt){for(var r=0;r<reservas.length;r++){if(enCaja(pt[0],pt[1],reservas[r])){pen+=50;break;}}});
      for(var z=0;z<pts.length;z++){var pp=pts[z];if(pp[0]<6||pp[1]<6||pp[0]>LW-6||pp[1]>LH-6){pen+=500;break;}}
      var bb=caja(pts);
      for(var m in burdas){
        var u2=aristas[m][0],v2=aristas[m][1],pts2=burdas[m];
        if(u===u2||v===v2){
          var dm=Math.hypot(pts[7][0]-pts2[7][0],pts[7][1]-pts2[7][1]);
          if(dm<38)pen+=3000/Math.max(dm,1);
        }
        if(u===u2||u===v2||v===u2||v===v2)continue;
        if(!solapan(bb,cajas[m]))continue;
        for(var a=0;a<NS;a++)for(var b=0;b<NS;b++){
          if(Math.hypot(pts[a][0]-pts2[b][0],pts[a][1]-pts2[b][1])<18)pen+=250;
          if(seCruzan(pts[a],pts[a+1],pts2[b],pts2[b+1]))pen+=60;
        }
      }
      if(!mejor||pen<mejor[0])mejor=[pen,ctrl,pts];
    });
    ctrls[kk]=mejor[1];burdas[kk]=mejor[2];cajas[kk]=caja(mejor[2]);
  });
  var curvas={};
  for(k=0;k<nA;k++){
    var l=[];for(i=0;i<=40;i++)l.push(bez(P[aristas[k][0]],ctrls[k],P[aristas[k][1]],i/40));
    curvas[k]=l;
  }
  var etqs={},rects=[];
  orden.forEach(function(kk){
    var texto=String(aristas[kk][2]),ew=texto.length*7.4+14,eh=20,mejor=null;
    [0.5,0.4,0.6,0.32,0.68,0.25,0.75,0.2,0.8].forEach(function(t){
      var pt=curvas[kk][Math.round(t*40)],cx=pt[0],cy=pt[1];
      var r=[cx-ew/2,cy-eh/2,cx+ew/2,cy+eh/2],pen=Math.abs(t-0.5)*20;
      for(var jj in P){
        var qx=clamp(P[jj][0],r[0],r[2]),qy=clamp(P[jj][1],r[1],r[3]);
        if(Math.hypot(P[jj][0]-qx,P[jj][1]-qy)<R+4)pen+=1200;
      }
      rects.concat(reservas).forEach(function(r2){
        if(!(r[2]+3<r2[0]||r2[2]+3<r[0]||r[3]+3<r2[1]||r2[3]+3<r[1]))pen+=1200;
      });
      for(var m in curvas){
        if(+m===kk)continue;
        var lista=curvas[m];
        for(var idx=0;idx<lista.length;idx+=2){if(enCaja(lista[idx][0],lista[idx][1],r)){pen+=100;break;}}
      }
      if(!mejor||pen<mejor[0])mejor=[pen,r,cx,cy,texto];
    });
    rects.push(mejor[1]);
    etqs[kk]=[mejor[2],mejor[3],mejor[1],mejor[4]];
  });
  return {curvas:curvas,etqs:etqs};
}
function nombreArista(u,v){return u+'-'+v;}
function guardarFormasAuto(P){
  var res=calcularRutas(P);
  formaAuto={};posPeso={};tamPeso={};
  for(var k in res.curvas){
    var kk=+k,u=aristas[kk][0],v=aristas[kk][1],p0=P[u],p1=P[v];
    var medio=res.curvas[k][20];
    var cx=2*medio[0]-0.5*(p0[0]+p1[0]),cy=2*medio[1]-0.5*(p0[1]+p1[1]);
    formaAuto[kk]=formaDeControl(p0,p1,[cx,cy]);
    var e=res.etqs[k],mi=20,md=1e18;
    for(var i=0;i<=40;i++){
      var dd=Math.pow(res.curvas[k][i][0]-e[0],2)+Math.pow(res.curvas[k][i][1]-e[1],2);
      if(dd<md){md=dd;mi=i;}
    }
    posPeso[kk]=mi;
    tamPeso[kk]=[(e[2][2]-e[2][0])/2,(e[2][3]-e[2][1])/2,e[3]];
  }
}
function asegurarFormas(){
  var clave=LW+','+LH+','+JSON.stringify(aristas);
  if(clave!==claveGuardada){guardarFormasAuto(Pbase);claveGuardada=clave;}
}
function curvaDe(k){
  var u=aristas[k][0],v=aristas[k][1],p0=Pbase[u],p1=Pbase[v],nom=nombreArista(u,v),a,b,pp;
  if(formaManual[nom]){a=formaManual[nom][0];b=formaManual[nom][1];pp=20;}
  else{a=formaAuto[k][0];b=formaAuto[k][1];pp=posPeso[k];}
  var ctrl=controlDeForma(p0,p1,a,b),l=[];
  for(var i=0;i<=40;i++)l.push(bez(p0,ctrl,p1,i/40));
  return {pts:l,pp:pp};
}

/* ---------- Dijkstra ---------- */
function guardarPaso(d,p,vis,it,actual,rel,log,fin){
  pasos.push({d:d.slice(),p:p.map(function(x){return x.slice();}),vis:vis.slice(),it:it.slice(),cur:actual,rel:rel.slice(),log:log.slice(),fin:fin});
}
function dijkstra(s,t){
  pasos=[];
  var d=[],p=[],vis=[],it=[],turno=0,i;
  for(i=0;i<n;i++){d.push(INF);p.push([]);vis.push(false);it.push(0);}
  d[s]=0;
  guardarPaso(d,p,vis,it,-1,[],['Inicio: d('+letra(s)+') = 0 y el resto de vértices tiene distancia ∞.'],false);
  while(true){
    var u=-1;
    for(i=0;i<n;i++)if(!vis[i]&&d[i]<INF&&(u<0||d[i]<d[u]))u=i;
    if(u<0)break;
    vis[u]=true;turno++;it[u]=turno;
    var log=['Se elige '+letra(u)+': es el vértice no visitado con menor distancia ('+d[u]+').'],rel=[];
    for(var k=0;k<aristas.length;k++){
      var a=aristas[k][0],v=aristas[k][1],w=aristas[k][2];
      if(a!==u||vis[v])continue;
      rel.push(k);
      var nd=d[u]+w,base=letra(u)+'→'+letra(v)+': '+d[u]+'+'+w+'='+nd;
      if(nd<d[v]){log.push(base+' < '+tdist(d[v])+'. Se actualiza d('+letra(v)+')='+nd+'.');d[v]=nd;p[v]=[u];}
      else if(nd===d[v]){log.push(base+', igual a d('+letra(v)+'). Se suma otro camino mínimo.');p[v].push(u);}
      else log.push(base+' > '+tdist(d[v])+'. No mejora.');
    }
    if(log.length===1)log.push(letra(u)+' no tiene aristas hacia vértices pendientes.');
    guardarPaso(d,p,vis,it,u,rel,log,false);
    if(u===t)break;
  }
  if(d[t]<INF)guardarPaso(d,p,vis,it,-1,[],['Fin: el destino '+letra(t)+' quedó fijado con distancia mínima '+d[t]+'.'],true);
  else guardarPaso(d,p,vis,it,-1,[],['Fin: '+letra(t)+' no es alcanzable desde '+letra(s)+'.'],true);
}
function buscarCaminos(v,p,s){
  if(v===s)return [[s]];
  var lista=[];
  p[v].forEach(function(u){buscarCaminos(u,p,s).forEach(function(q){lista.push(q.concat([v]));});});
  return lista;
}

/* ---------- dibujo ---------- */
function se(tag,attrs,parent){
  var e=document.createElementNS(NS_SVG,tag);
  for(var k in attrs)e.setAttribute(k,attrs[k]);
  if(parent)parent.appendChild(e);
  return e;
}
function setTam(){
  var cw=canvas.clientWidth,ch=canvas.clientHeight;
  svg.setAttribute('viewBox','0 0 '+cw+' '+ch);
}
function aplicarTransform(){
  if(gRoot)gRoot.setAttribute('transform','translate('+panX+' '+panY+') scale('+zoom+')');
}
function etiquetaNodo(g,x,y,segs,fondo,borde,bold){
  var fs=11,len=0;
  segs.forEach(function(s){len+=s[0].length;});
  var w=len*fs*0.6+10,h=fs+8;
  se('rect',{x:x-w/2,y:y-h/2,width:w,height:h,rx:3,style:'fill:var('+fondo+');stroke:var('+borde+');stroke-width:1'},g);
  var t=se('text',{x:x,y:y,'text-anchor':'middle','dominant-baseline':'central','class':'lab'+(bold?' b':'')},g);
  segs.forEach(function(s){se('tspan',{style:'fill:var('+s[1]+')'},t).textContent=s[0];});
}
function dibujar(){
  svg.textContent='';
  gRoot=null;
  if(n===0||!cols.length)return;
  setTam();
  asegurarFormas();
  var R=radioNodo(),st=pasos.length?pasos[paso]:null,i,k;
  var g=se('g',{},svg);gRoot=g;aplicarTransform();

  var enCamino={};
  if(st&&st.fin&&st.d[dst]<INF){
    buscarCaminos(dst,st.p,src).forEach(function(q){for(var j=0;j<q.length-1;j++)enCamino[q[j]+'>'+q[j+1]]=true;});
  }
  var curvas={};etqBase={};
  for(k=0;k<aristas.length;k++){
    if(!formaAuto[k])continue;
    var c=curvaDe(k);curvas[k]=c.pts;
    var pt=c.pts[c.pp];
    etqBase[k]={cx:pt[0],cy:pt[1],mw:tamPeso[k][0],mh:tamPeso[k][1],text:tamPeso[k][2]};
  }
  var estilo={};
  for(k=0;k<aristas.length;k++){
    var u=aristas[k][0],v=aristas[k][1];
    if(enCamino[u+'>'+v])estilo[k]={col:'--acc',w:4,fill:'--accl',prio:2,txt:'--ink'};
    else if(st&&st.rel.indexOf(k)>=0)estilo[k]={col:'--ink',w:3,fill:'--rel-fill',prio:1,txt:'--ink'};
    else{var ec='--e'+(k%10);estilo[k]={col:ec,w:2,fill:'--card',prio:0,txt:ec};}
  }
  for(var prio=0;prio<3;prio++){
    for(k=0;k<aristas.length;k++){
      if(!curvas[k]||estilo[k].prio!==prio)continue;
      var u2=aristas[k][0],v2=aristas[k][1],pts=curvas[k].slice();
      while(pts.length>2&&Math.hypot(pts[0][0]-Pbase[u2][0],pts[0][1]-Pbase[u2][1])<R)pts.shift();
      while(pts.length>2&&Math.hypot(pts[pts.length-1][0]-Pbase[v2][0],pts[pts.length-1][1]-Pbase[v2][1])<R+3)pts.pop();
      var s=estilo[k];
      se('polyline',{points:pts.map(function(p){return p[0].toFixed(1)+','+p[1].toFixed(1);}).join(' '),
        style:'fill:none;stroke:var('+s.col+');stroke-width:'+s.w+';stroke-linecap:round;stroke-linejoin:round'},g);
      var e1=pts[pts.length-1],e0=pts[Math.max(0,pts.length-3)];
      var ang=Math.atan2(e1[1]-e0[1],e1[0]-e0[0]),L=11,Wd=5.5;
      var bx=e1[0]-L*Math.cos(ang),by=e1[1]-L*Math.sin(ang);
      se('polygon',{points:e1[0].toFixed(1)+','+e1[1].toFixed(1)+' '+(bx-Wd*Math.sin(ang)).toFixed(1)+','+(by+Wd*Math.cos(ang)).toFixed(1)+' '+(bx+Wd*Math.sin(ang)).toFixed(1)+','+(by-Wd*Math.cos(ang)).toFixed(1),
        style:'fill:var('+s.col+')'},g);
    }
  }
  for(i in Pbase){
    var x=Pbase[i][0],y=Pbase[i][1],ii=+i;
    var esSel=modo==='man'&&(nodoSel===ii||nodoSel2===ii);
    if(esSel)se('circle',{cx:x,cy:y,r:R+9,style:'fill:none;stroke:var(--cur);stroke-width:3;stroke-dasharray:4 3'},g);
    if(ii===src)se('circle',{cx:x,cy:y,r:R+5,style:'fill:none;stroke:var(--acc);stroke-width:2'},g);
    if(ii===dst)se('circle',{cx:x,cy:y,r:R+5,style:'fill:none;stroke:var(--ink);stroke-width:1.5;stroke-dasharray:4 3'},g);
    var fill='--card',bor='--ink',gr=1.5;
    if(esSel||(st&&st.cur===ii)){fill='--curl';bor='--cur';gr=3;}
    else if(st&&st.vis[ii])fill='--accl';
    se('circle',{cx:x,cy:y,r:R,style:'fill:var('+fill+');stroke:var('+bor+');stroke-width:'+gr},g);
    se('text',{x:x,y:y,'text-anchor':'middle','dominant-baseline':'central','class':'nl',style:'fill:var(--ink)'},g).textContent=letra(ii);
  }
  if(st){
    for(i in Pbase){
      var ii2=+i,px=Pbase[i][0],py=Pbase[i][1];
      var pr=st.p[ii2].map(letra).join('/');if(pr==='')pr='–';
      var segs=[['[','--mut'],[tdist(st.d[ii2]),'--dist'],[', ','--mut'],[pr,'--pred'],[']','--mut']];
      if(st.it[ii2]!==0){segs.push(['(','--mut']);segs.push([String(st.it[ii2]),'--itr']);segs.push([')','--mut']);}
      var fo,bo,bold;
      if(st.cur===ii2){fo='--curl';bo='--cur';bold=true;}
      else if(st.vis[ii2]){fo='--accl';bo='--acc';bold=true;}
      else{fo='--card';bo='--line';bold=false;}
      etiquetaNodo(g,px,py-R-13,segs,fo,bo,bold);
    }
  }
  for(prio=0;prio<3;prio++){
    for(k in etqBase){
      if(estilo[k].prio!==prio)continue;
      var e=etqBase[k],sk=estilo[k];
      se('rect',{x:e.cx-e.mw,y:e.cy-e.mh,width:e.mw*2,height:e.mh*2,rx:4,style:'fill:var('+sk.fill+');stroke:var('+sk.col+');stroke-width:1.5'},g);
      se('text',{x:e.cx,y:e.cy,'text-anchor':'middle','dominant-baseline':'central','class':'wl',style:'fill:var('+sk.txt+')'},g).textContent=e.text;
    }
  }
  var lg=$('legend');
  if(st)lg.innerHTML='Etiqueta: [<span class="d">distancia</span>, <span class="p">predecesor</span>](<span class="i">iteración</span>)';
  else lg.textContent='';
}

/* ---------- vista (zoom / pan / ajuste) ---------- */
function ajustar(){
  if(!cols.length)return;
  var cw=canvas.clientWidth,ch=canvas.clientHeight;
  if(!cw||!ch)return;
  asegurarFormas();
  var pts=[],i;
  for(i in Pbase)pts.push(Pbase[i]);
  for(var k=0;k<aristas.length;k++){
    if(!formaAuto[k])continue;
    var c=curvaDe(k).pts;
    for(i=0;i<=40;i+=4)pts.push(c[i]);
  }
  var bb=caja(pts),R=radioNodo();
  var mL=R+16,mT=R+34,mB=R+16;
  var bw=Math.max(bb[2]-bb[0],100),bh=Math.max(bb[3]-bb[1],100);
  zoom=clamp(Math.min((cw-2*mL)/bw,(ch-mT-mB)/bh),0.3,1.5);
  panX=(cw-(bb[0]+bb[2])*zoom)/2;
  panY=mT+(ch-mT-mB-bh*zoom)/2-bb[1]*zoom+(bh-(bb[3]-bb[1]))*zoom/2;
  tocado=false;
  dibujar();
}
function zoomEn(factor,sx,sy){
  var nz=clamp(zoom*factor,0.2,4);
  if(nz===zoom)return;
  var bx=(sx-panX)/zoom,by=(sy-panY)/zoom;
  zoom=nz;panX=sx-bx*zoom;panY=sy-by*zoom;
  tocado=true;aplicarTransform();cerrarEditor();
}

/* ---------- mensajes y controles ---------- */
function msg(t,info){var m=$('msg');m.textContent=t||'';m.className=info?'info':'';}
function estadoControles(on){['bIni','bAnt','bSig','bFin'].forEach(function(id){$(id).disabled=!on;});}
function textoAristas(){
  var t=$('listaAristas');
  if(!aristas.length)t.textContent='Aristas: ninguna. Añade aristas para empezar.';
  else t.textContent='Aristas: '+aristas.map(function(a){return letra(a[0])+'→'+letra(a[1])+' ('+a[2]+')';}).join(', ');
}
function llenarSelects(){
  var html='';for(var i=0;i<n;i++)html+='<option value="'+i+'">'+letra(i)+'</option>';
  $('selOrigen').innerHTML=html;$('selDestino').innerHTML=html;
  $('selOrigen').value=String(src);$('selDestino').value=String(dst);
}
function leerPesoMax(){
  var t=$('pesoMax').value.trim();
  if(t==='')return PM_DEF;
  var v=parseInt(t,10);
  if(!/^\d+$/.test(t)||v<1||v>PM_LIM){
    $('pesoMax').value='';
    msg('El peso máximo debe ser un entero entre 1 y '+PM_LIM+'. Se usó '+PM_DEF+'.');
    return PM_DEF;
  }
  return v;
}
function generar(){
  formaManual={};movNodos={};
  var t=$('n').value.trim(),c=parseInt(t,10);
  if(!/^\d+$/.test(t)||c<N_MIN||c>N_MAX){
    c=8;$('n').value='8';
    msg('El número de nodos debe ser un entero entre '+N_MIN+' y '+N_MAX+'.');
  }else msg('');
  n=c;
  if(src>=n)src=0;
  if(dst>=n)dst=n-1;
  if(modo==='rand')aristas=generarAleatorio(n,leerPesoMax());else aristas=[];
  llenarSelects();
  reiniciar(true);
}
function reiniciar(rearmar){
  if(rearmar===undefined)rearmar=true;
  cerrarEditor();
  nodoSel=null;nodoSel2=null;
  pasos=[];paso=0;
  estadoControles(false);
  $('etiquetaPaso').textContent='';
  $('tabla').innerHTML='';$('log').innerHTML='';$('res').innerHTML='';
  textoAristas();
  if(rearmar){
    calcularPosiciones();tamanoLogico();actualizarPosiciones();
    claveGuardada=null;ajustar();
  }else dibujar();
}
function mostrarPaso(){
  var st=pasos[paso];
  $('etiquetaPaso').textContent='Paso '+(paso+1)+' de '+pasos.length;
  var h='';
  for(var v=0;v<n;v++){
    var estado,tag;
    if(st.cur===v){estado='actual';tag='cur';}
    else if(st.vis[v]){estado='visitado';tag='vis';}
    else{estado='pendiente';tag='';}
    var pr=st.p[v].map(letra).join(', ')||'–';
    h+='<tr class="'+tag+'"><td>'+letra(v)+'</td><td>'+tdist(st.d[v])+'</td><td>'+pr+'</td><td>'+estado+'</td></tr>';
  }
  $('tabla').innerHTML=h;
  $('log').innerHTML=st.log.map(function(l){return '<li>'+l+'</li>';}).join('');
  var res=$('res');res.innerHTML='';
  if(st.fin){
    if(st.d[dst]<INF){
      var lista=buscarCaminos(dst,st.p,src);
      var s='<b>Distancia mínima '+letra(src)+'→'+letra(dst)+': '+st.d[dst]+'</b><br>Caminos mínimos: '+lista.length;
      lista.forEach(function(q){s+='<br><span class="path">'+q.map(letra).join(' → ')+'</span>';});
      res.innerHTML=s;
    }else res.innerHTML='<b>No existe camino de '+letra(src)+' a '+letra(dst)+'.</b>';
  }else res.innerHTML='<span class="empty">El resultado aparece en el último paso.</span>';
  dibujar();
}
function ejecutar(){
  if(src===dst){msg('El origen y el destino deben ser distintos.');return;}
  if(!aristas.length){msg('Primero construye el grafo.');return;}
  msg('');
  dijkstra(src,dst);paso=0;estadoControles(true);mostrarPaso();
}
function irAPaso(k){
  if(!pasos.length)return;
  paso=clamp(k,0,pasos.length-1);mostrarPaso();
}

/* ---------- modo manual ---------- */
function leerAristas(texto){
  var nuevas=[],errores=[];
  var re=/([A-Za-z])\s*(?:->|→|=>|>|-|,|:)?\s*([A-Za-z])\s*[:=,]?\s*(\d+(?:\.\d+)?)/g,m;
  while((m=re.exec(texto))!==null){
    var u=m[1].toUpperCase().charCodeAt(0)-65,v=m[2].toUpperCase().charCodeAt(0)-65,w=parseFloat(m[3]);
    if(u>=n||v>=n){
      errores.push('El vértice '+(u>=n?m[1].toUpperCase():m[2].toUpperCase())+' no existe (los vértices son '+letra(0)+'–'+letra(n-1)+').');
      continue;
    }
    nuevas.push([u,v,w]);
  }
  var resto=texto.replace(/([A-Za-z])\s*(?:->|→|=>|>|-|,|:)?\s*([A-Za-z])\s*[:=,]?\s*(\d+(?:\.\d+)?)/g,' ').replace(/[\s,;]+/g,' ').trim();
  if(resto!=='')errores.push('No se entendió: "'+resto+'".');
  return {nuevas:nuevas,errores:errores};
}
function anadir(){
  var ent=$('entrada'),texto=ent.value.trim();
  if(texto===''){msg('Escribe una arista, por ejemplo: A B 5 (o AB5).',true);return;}
  var r=leerAristas(texto),agregadas=0;
  r.nuevas.forEach(function(a){
    var err=validarArista(a[0],a[1],a[2]);
    if(err)r.errores.push(err);
    else{aristas.push(a);ultimoPeso=String(a[2]);agregadas++;}
  });
  if(agregadas>0){nodoSel=null;nodoSel2=null;reiniciar();ent.value='';}
  if(r.errores.length){
    msg(r.errores.slice(0,2).join('  ')+(r.errores.length>2?'  (+'+(r.errores.length-2)+' más)':''));
  }else if(agregadas>0)msg(agregadas+' arista(s) añadida(s).',true);
  ent.focus();
}
function quitar(){
  if(!aristas.length)return;
  var u=aristas.pop();
  delete formaManual[nombreArista(u[0],u[1])];
  reiniciar();msg('');
}
function limpiar(){aristas=[];formaManual={};reiniciar();msg('');}
function clickNodo(elegido){
  if(modo!=='man')return;
  var ent=$('entrada');
  if(elegido===null){nodoSel=null;nodoSel2=null;msg('');}
  else if(nodoSel===null){nodoSel=elegido;nodoSel2=null;msg('Salida: '+letra(elegido)+' seleccionado. Toca el vértice de llegada.',true);}
  else if(nodoSel===elegido){nodoSel=null;nodoSel2=null;msg('Selección cancelada.',true);}
  else{
    nodoSel2=elegido;
    var pref=letra(nodoSel)+' '+letra(elegido)+' ';
    ent.value=pref+ultimoPeso;
    ent.focus();
    try{ent.setSelectionRange(pref.length,ent.value.length);}catch(e){}
    msg('Arista '+letra(nodoSel)+'→'+letra(elegido)+' preparada. Escribe el peso y pulsa Enter.',true);
  }
  dibujar();
}

/* ---------- edición de peso ---------- */
function cerrarEditor(){
  if(editor){var e=editor;editor=null;if(e.parentNode)e.parentNode.removeChild(e);}
}
function abrirEditor(k){
  cerrarEditor();
  var e=etqBase[k];if(!e)return;
  editorK=k;
  var inp=document.createElement('input');
  inp.className='editor';inp.type='text';inp.setAttribute('inputmode','decimal');
  inp.id='editorPeso';inp.value=String(aristas[k][2]);
  inp.style.left=(e.cx*zoom+panX-32)+'px';inp.style.top=(e.cy*zoom+panY-15)+'px';
  canvas.appendChild(inp);editor=inp;
  inp.focus();inp.select();
  var cancelado=false;
  inp.addEventListener('keydown',function(ev){
    if(ev.key==='Enter'){aceptarEditor();}
    else if(ev.key==='Escape'){cancelado=true;cerrarEditor();}
    ev.stopPropagation();
  });
  inp.addEventListener('blur',function(){
    if(cancelado||editor!==inp)return;
    var t=inp.value.trim();
    if(/^\d+(\.\d+)?$/.test(t)&&parseFloat(t)>0)aceptarEditor();else cerrarEditor();
  });
}
function aceptarEditor(){
  if(!editor)return;
  var k=editorK,t=editor.value.trim();
  if(!/^\d+(\.\d+)?$/.test(t)){msg('El peso debe ser un número positivo (por ejemplo 5 o 2.5).');return;}
  var nuevo=parseFloat(t);
  if(!(nuevo>0)){msg('El peso debe ser un número positivo.');return;}
  cerrarEditor();
  aristas[k][2]=nuevo;
  reiniciar(false);
  msg('Peso de la arista '+letra(aristas[k][0])+'→'+letra(aristas[k][1])+' cambiado a '+nuevo+'.',true);
  textoAristas();
}

/* ---------- punteros: arrastre, pellizco y toque ---------- */
var ptrs={},nPtr=0,drag=null,pinch=null;
function aBase(e){
  var r=svg.getBoundingClientRect();
  var sx=e.clientX-r.left,sy=e.clientY-r.top;
  return {sx:sx,sy:sy,x:(sx-panX)/zoom,y:(sy-panY)/zoom};
}
function etiquetaEn(x,y){
  var m=7/zoom,ks=Object.keys(etqBase).reverse();
  for(var i=0;i<ks.length;i++){
    var e=etqBase[ks[i]];
    if(x>=e.cx-e.mw-m&&x<=e.cx+e.mw+m&&y>=e.cy-e.mh-m&&y<=e.cy+e.mh+m)return +ks[i];
  }
  return null;
}
function nodoEn(x,y){
  var lim=radioNodo()+6+4/zoom,mejor=null,md=1e9;
  for(var i in Pbase){
    var d=Math.hypot(x-Pbase[i][0],y-Pbase[i][1]);
    if(d<=lim&&d<md){md=d;mejor=+i;}
  }
  return mejor;
}
svg.addEventListener('pointerdown',function(e){
  if(e.button!==undefined&&e.button>0)return;
  try{svg.setPointerCapture(e.pointerId);}catch(x){}
  if(!ptrs[e.pointerId])nPtr++;
  ptrs[e.pointerId]={x:e.clientX,y:e.clientY};
  if(nPtr===2){
    drag=null;
    var ids=Object.keys(ptrs),a=ptrs[ids[0]],b=ptrs[ids[1]];
    pinch={d:Math.hypot(a.x-b.x,a.y-b.y)||1,z:zoom,bx:0,by:0};
    var r=svg.getBoundingClientRect(),mx=(a.x+b.x)/2-r.left,my=(a.y+b.y)/2-r.top;
    pinch.bx=(mx-panX)/zoom;pinch.by=(my-panY)/zoom;
    cerrarEditor();return;
  }
  if(nPtr>2)return;
  cerrarEditor();
  var p=aBase(e),k=etiquetaEn(p.x,p.y);
  if(k!==null&&k<aristas.length){drag={t:'peso',k:k,ox:p.x-etqBase[k].cx,oy:p.y-etqBase[k].cy,x0:e.clientX,y0:e.clientY,moved:false};return;}
  var nd=nodoEn(p.x,p.y);
  if(nd!==null){drag={t:'nodo',i:nd,ox:p.x-Pbase[nd][0],oy:p.y-Pbase[nd][1],x0:e.clientX,y0:e.clientY,moved:false};return;}
  drag={t:'fondo',x0:e.clientX,y0:e.clientY,px:panX,py:panY,moved:false};
});
svg.addEventListener('pointermove',function(e){
  if(!ptrs[e.pointerId])return;
  ptrs[e.pointerId]={x:e.clientX,y:e.clientY};
  if(pinch&&nPtr===2){
    var ids=Object.keys(ptrs),a=ptrs[ids[0]],b=ptrs[ids[1]];
    var d=Math.hypot(a.x-b.x,a.y-b.y)||1,r=svg.getBoundingClientRect();
    var mx=(a.x+b.x)/2-r.left,my=(a.y+b.y)/2-r.top;
    zoom=clamp(pinch.z*d/pinch.d,0.2,4);
    panX=mx-pinch.bx*zoom;panY=my-pinch.by*zoom;
    tocado=true;aplicarTransform();return;
  }
  if(!drag)return;
  if(!drag.moved&&Math.hypot(e.clientX-drag.x0,e.clientY-drag.y0)<5)return;
  drag.moved=true;canvas.classList.add('moving');
  if(drag.t==='fondo'){
    panX=drag.px+e.clientX-drag.x0;panY=drag.py+e.clientY-drag.y0;
    tocado=true;aplicarTransform();return;
  }
  var p=aBase(e);
  if(drag.t==='nodo'){
    var i=drag.i,au=Pauto[i];
    movNodos[i]=[p.x-drag.ox-au[0],p.y-drag.oy-au[1]];
    actualizarPosiciones();dibujar();return;
  }
  if(drag.t==='peso'){
    var k=drag.k,u=aristas[k][0],v=aristas[k][1],p0=Pbase[u],p1=Pbase[v];
    var mx2=p.x-drag.ox,my2=p.y-drag.oy;
    var f=formaDeControl(p0,p1,[2*mx2-0.5*(p0[0]+p1[0]),2*my2-0.5*(p0[1]+p1[1])]);
    formaManual[nombreArista(u,v)]=[clamp(f[0],-1.5,2.5),clamp(f[1],-3,3)];
    dibujar();
  }
});
function soltar(e){
  if(!ptrs[e.pointerId])return;
  delete ptrs[e.pointerId];nPtr=Math.max(0,nPtr-1);
  if(pinch){if(nPtr<2)pinch=null;drag=null;canvas.classList.remove('moving');return;}
  var d=drag;drag=null;canvas.classList.remove('moving');
  if(!d||d.moved||e.type==='pointercancel')return;
  if(d.t==='nodo')clickNodo(d.i);
  else if(d.t==='fondo')clickNodo(null);
  else if(d.t==='peso'){
    var ahora=Date.now();
    if(lastTap.k===d.k&&ahora-lastTap.t<420){lastTap={k:-1,t:0};abrirEditor(d.k);}
    else lastTap={k:d.k,t:ahora};
  }
}
svg.addEventListener('pointerup',soltar);
svg.addEventListener('pointercancel',soltar);
svg.addEventListener('wheel',function(e){
  e.preventDefault();
  var r=svg.getBoundingClientRect();
  zoomEn(e.deltaY<0?1.12:1/1.12,e.clientX-r.left,e.clientY-r.top);
},{passive:false});

/* ---------- eventos de la interfaz ---------- */
function cambiarModo(){
  var m=document.querySelector('input[name="modo"]:checked').value;
  modo=m;
  $('manual').hidden=(m!=='man');
  $('filaPeso').hidden=(m==='man');
  canvas.style.cursor='';
  generar();
}
Array.prototype.forEach.call(document.querySelectorAll('input[name="modo"]'),function(r){r.addEventListener('change',cambiarModo);});
$('btnGen').addEventListener('click',generar);
$('n').addEventListener('keydown',function(e){if(e.key==='Enter')generar();});
$('pesoMax').addEventListener('keydown',function(e){if(e.key==='Enter')generar();});
$('btnAnadir').addEventListener('click',anadir);
$('btnQuitar').addEventListener('click',quitar);
$('btnLimpiar').addEventListener('click',limpiar);
$('entrada').addEventListener('keydown',function(e){
  if(e.key==='Enter')anadir();
  else if(e.key==='Escape'){$('entrada').value='';reiniciar();}
});
$('selOrigen').addEventListener('change',function(){src=+this.value;reiniciar(false);});
$('selDestino').addEventListener('change',function(){dst=+this.value;reiniciar(false);});
$('btnEjecutar').addEventListener('click',ejecutar);
$('bIni').addEventListener('click',function(){irAPaso(0);});
$('bAnt').addEventListener('click',function(){irAPaso(paso-1);});
$('bSig').addEventListener('click',function(){irAPaso(paso+1);});
$('bFin').addEventListener('click',function(){irAPaso(pasos.length-1);});
$('zMas').addEventListener('click',function(){zoomEn(1.2,canvas.clientWidth/2,canvas.clientHeight/2);});
$('zMenos').addEventListener('click',function(){zoomEn(1/1.2,canvas.clientWidth/2,canvas.clientHeight/2);});
$('zAjustar').addEventListener('click',ajustar);
document.addEventListener('keydown',function(e){
  var t=e.target&&e.target.tagName;
  if(t==='INPUT'||t==='SELECT'||t==='TEXTAREA')return;
  if(e.key==='ArrowRight')irAPaso(paso+1);
  else if(e.key==='ArrowLeft')irAPaso(paso-1);
});
if(window.ResizeObserver){
  var ultimoAncho=0;
  new ResizeObserver(function(){
    var cw=canvas.clientWidth;
    setTam();
    if(!tocado&&cw!==ultimoAncho)ajustar();
    ultimoAncho=cw;
  }).observe(canvas);
}
if(document.fonts&&document.fonts.ready)document.fonts.ready.then(function(){if(!tocado)dibujar();});

generar();
})();
