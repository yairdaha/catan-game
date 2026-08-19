import { initializeApp } from "https://www.gstatic.com/firebasejs/12.17.1/firebase-app.js";
import { getDatabase, ref, get, set, onValue, runTransaction } from "https://www.gstatic.com/firebasejs/12.17.1/firebase-database.js";

const firebaseConfig={apiKey:"AIzaSyA9dxSGE_bsJn7YEOf4wYu8vpNXfFDgsTc",authDomain:"catan-44838.firebaseapp.com",databaseURL:"https://catan-44838-default-rtdb.europe-west1.firebasedatabase.app",projectId:"catan-44838",storageBucket:"catan-44838.firebasestorage.app",messagingSenderId:"296003162886",appId:"1:296003162886:web:7b83fd4563a0453edd8487",measurementId:"G-8CCGZKJ9JW"};
const R={wood:{name:"פרחים",icon:"🌸",color:"#d995b6"},brick:{name:"חול",icon:"🏖️",color:"#d7bd86"},sheep:{name:"חסות",icon:"🥬",color:"#75c178"},ore:{name:"זרעים",icon:"🌱",color:"#7db196"},wheat:{name:"עגבניות שרי",icon:"🍅",color:"#d96a55"},desert:{name:"דיונה",icon:"🏜️",color:"#c7a86b"}};
const RK=['wood','brick','sheep','ore','wheat'];
const PC=['#4da1ff','#ef5b5b','#2db571','#f0a62b'];
const COST={road:{wood:1,brick:1},settlement:{wood:1,brick:1,sheep:1,wheat:1},city:{ore:3,wheat:2},dev:{sheep:1,ore:1,wheat:1}};
const GUSH_SETTLEMENT_NAMES=[
 "אלי סיני","בדולח","בני עצמון","גדיד","גן אור","גני טל","דוגית",
 "כפר דרום","כפר ים","כרם עצמונה","מורג","נווה דקלים","ניסנית",
 "נצר חזני","נצרים","פאת שדה","קטיף","רפיח ים","שירת הים","שליו","תל קטיפא"
];
const DEV_NAMES={knight:"מחבל",roadBuilding:"פריצת דרך",yearPlenty:"יבול מבורך",monopoly:"שיווק מרוכז",vp_greenhouse:"חממה מצטיינת",vp_farm:"משק השנה",vp_village:"יישוב פורח",vp_agri:"חקלאות פורצת דרך",vp_community:"קהילה חזקה"};
const VP_TYPES=new Set(['vp_greenhouse','vp_farm','vp_village','vp_agri','vp_community']);
const CENTERS=[[215,92],[305,92],[395,92],[170,170],[260,170],[350,170],[440,170],[125,248],[215,248],[305,248],[395,248],[485,248],[170,326],[260,326],[350,326],[440,326],[215,404],[305,404],[395,404]];
const HEXR=52,GRAPH=buildGraph();
let db=null,unsub=null,ready=false,ferr='',state=null,screen='home',err='',uiMode=null,modal=null,lastAlertedTurnKey=null,turnToastTimer=null,lastSeenStealId=null,stealToastTimer=null;
let myId=localStorage.getItem('myId')||crypto.randomUUID();localStorage.setItem('myId',myId);
let myName=localStorage.getItem('myName')||'';
let code=new URLSearchParams(location.search).get('room')?.toUpperCase()||'';

function buildGraph(){const verts=[],vmap=new Map(),edges=[],emap=new Map(),tileVerts=[];const key=(x,y)=>`${x.toFixed(1)},${y.toFixed(1)}`;const gv=(x,y)=>{const k=key(x,y);if(!vmap.has(k)){vmap.set(k,verts.length);verts.push({id:verts.length,x,y,tiles:[]})}return vmap.get(k)};CENTERS.forEach(([cx,cy],ti)=>{const vs=[];for(let i=0;i<6;i++){const a=(60*i-30)*Math.PI/180,x=cx+HEXR*Math.cos(a),y=cy+HEXR*Math.sin(a),v=gv(x,y);vs.push(v);if(!verts[v].tiles.includes(ti))verts[v].tiles.push(ti)}tileVerts[ti]=vs;for(let i=0;i<6;i++){const a=vs[i],b=vs[(i+1)%6],k=a<b?`${a}-${b}`:`${b}-${a}`;let e=emap.get(k);if(e===undefined){e=edges.length;emap.set(k,e);edges.push({id:e,a,b,tiles:[]})}if(!edges[e].tiles.includes(ti))edges[e].tiles.push(ti)}});const boundary=edges.filter(e=>e.tiles.length===1).map(e=>{const a=verts[e.a],b=verts[e.b],x=(a.x+b.x)/2,y=(a.y+b.y)/2;return{...e,x,y,ang:Math.atan2(y-248,x-305)}}).sort((a,b)=>a.ang-b.ang);return{verts,edges,tileVerts,boundary}}
function ps(s=state){return Array.isArray(s?.players)?s.players:Object.values(s?.players||{})}
function clean(c){return(c||'').trim().toUpperCase().replace(/[^A-Z0-9]/g,'').slice(0,4)}
function roomRef(c){return ref(db,`games/${clean(c)}`)}
function randInt(max){
 const range=0x100000000-(0x100000000%max);
 const buf=new Uint32Array(1);
 do{crypto.getRandomValues(buf)}while(buf[0]>=range);
 return buf[0]%max
}
function shuffle(a){
 a=[...a];
 for(let i=a.length-1;i>0;i--){
   const j=randInt(i+1);
   [a[i],a[j]]=[a[j],a[i]]
 }
 return a
}
function blank(){return{wood:0,brick:0,sheep:0,ore:0,wheat:0}}
function has(p,c){return Object.entries(c).every(([k,v])=>Number(p?.resources?.[k]||0)>=Number(v))}
function total(p){return RK.reduce((a,k)=>a+(p.resources?.[k]||0),0)}
function newCode(){const ch='ABCDEFGHJKLMNPQRSTUVWXYZ23456789';let x='';for(let i=0;i<4;i++)x+=ch[Math.floor(Math.random()*ch.length)];return x}
function newDevDeck(){return shuffle(['knight','knight','knight','knight','knight','knight','knight','knight','knight','knight','knight','knight','knight','knight','roadBuilding','roadBuilding','yearPlenty','yearPlenty','monopoly','monopoly','vp_greenhouse','vp_farm','vp_village','vp_agri','vp_community'])}
function tileAdjacency(){
 const adj=Array.from({length:19},()=>new Set());
 for(const e of GRAPH.edges){
   if(e.tiles?.length===2){
     const [a,b]=e.tiles;
     adj[a].add(b);adj[b].add(a);
   }
 }
 return adj.map(s=>[...s])
}
const TILE_ADJ=tileAdjacency();

function validNumberLayout(tiles){
 for(let i=0;i<tiles.length;i++){
   const a=tiles[i].number;
   if(a==null)continue;
   for(const j of TILE_ADJ[i]){
     if(j<=i)continue;
     const b=tiles[j].number;
     if(b==null)continue;
     if(a===b)return false;
     if((a===6||a===8)&&(b===6||b===8))return false;
   }
 }
 return true
}

function generateBoard(){
 const resourcePool=['wood','wood','wood','wood','brick','brick','brick','sheep','sheep','sheep','sheep','ore','ore','ore','wheat','wheat','wheat','wheat','desert'];

 // Generate several independent random layouts and choose one that avoids obvious clumps.
 // Counts stay identical to standard Catan - only positions change.
 let res=null,bestScore=Infinity;
 for(let attempt=0;attempt<32;attempt++){
   const candidate=shuffle(resourcePool);
   let score=0;
   for(let i=0;i<candidate.length;i++){
     for(const j of TILE_ADJ[i]){
       if(j<=i)continue;
       if(candidate[i]===candidate[j] && candidate[i]!=='desert')score+=3;
     }
   }
   // Extra penalty if one tile touches two or more tiles of the same resource.
   for(let i=0;i<candidate.length;i++){
     if(candidate[i]==='desert')continue;
     const same=TILE_ADJ[i].filter(j=>candidate[j]===candidate[i]).length;
     if(same>=2)score+=(same-1)*5;
   }
   if(score<bestScore){bestScore=score;res=candidate}
   if(score===0)break;
 }
 const numberPool=[2,3,3,4,4,5,5,6,6,8,8,9,9,10,10,11,11,12];
 let tiles=null;

 // Re-roll only the number placement until it obeys both adjacency rules.
 // 10,000 is deliberately generous; in practice a valid layout is found quickly.
 for(let attempt=0;attempt<10000;attempt++){
   const nums=shuffle(numberPool);
   let n=0;
   const candidate=res.map((resource,id)=>({
     id,
     resource,
     number:resource==='desert'?null:nums[n++]
   }));
   if(validNumberLayout(candidate)){
     tiles=candidate;
     break;
   }
 }
 if(!tiles)throw new Error('לא נמצא סידור מספרים תקין ללוח');

 const b=GRAPH.boundary;
 const idx=[0,3,7,10,13,17,20,23,27];
 const types=shuffle(['any','any','any','any','wood','brick','sheep','ore','wheat']);
 return{
   tiles,
   robber:tiles.findIndex(t=>t.resource==='desert'),
   ports:idx.map((x,i)=>({edgeId:b[x%b.length].id,type:types[i]}))
 }
}
function myIndex(s=state){return ps(s).findIndex(p=>p.id===myId)}
function isActivePlayer(p){return p && !p.left}
function activePlayerIndexes(s){return s.players.map((p,i)=>isActivePlayer(p)?i:-1).filter(i=>i>=0)}
function nextActivePlayer(s,from){
 const active=activePlayerIndexes(s);
 if(!active.length)return null;
 for(let step=1;step<=s.players.length;step++){
   const i=(from+step)%s.players.length;
   if(isActivePlayer(s.players[i]))return i
 }
 return active[0]
}
function spectators(s=state){return Array.isArray(s?.spectators)?s.spectators:Object.values(s?.spectators||{})}
function normalizeSpectators(s){s.spectators=spectators(s);return s.spectators}
function isSpectator(s=state){return spectators(s).some(x=>x.id===myId)}

function building(s,v){return s.buildings?.[v]||null}
function road(s,e){const x=s.roads?.[e];return x===undefined?null:x}
function adjV(v){const o=[];GRAPH.edges.forEach(e=>{if(e.a===v)o.push(e.b);else if(e.b===v)o.push(e.a)});return o}
function adjE(v){return GRAPH.edges.filter(e=>e.a===v||e.b===v).map(e=>e.id)}
function validSettlement(s,v,pi,setup=false){if(building(s,v))return false;if(adjV(v).some(x=>building(s,x)))return false;if(setup)return true;return adjE(v).some(e=>road(s,e)===pi)}
function canRoad(s,eid,pi){if(road(s,eid)!==null)return false;const e=GRAPH.edges[eid];for(const v of[e.a,e.b]){const b=building(s,v);if(b?.owner===pi)return true;if(b&&b.owner!==pi)continue;if(adjE(v).some(x=>road(s,x)===pi))return true}return false}
function pieceCount(s,pi,type){if(type==='road')return Object.values(s.roads||{}).filter(o=>o===pi).length;if(type==='settlement')return Object.values(s.buildings||{}).filter(b=>b.owner===pi&&b.level==='settlement').length;if(type==='city')return Object.values(s.buildings||{}).filter(b=>b.owner===pi&&b.level==='city').length;return 0}
function pay(s,pi,c){
 for(const[k,v]of Object.entries(c)){
   s.players[pi].resources[k]=Number(s.players[pi].resources[k]||0)-Number(v);
   s.bank[k]=Number(s.bank[k]||0)+Number(v)
 }
}
function takeBank(s,pi,k,n){if((s.bank[k]||0)<n)return false;s.bank[k]-=n;s.players[pi].resources[k]+=n;return true}
function portRates(s,pi){let any=false;const sp=new Set();for(const p of s.board.ports){const e=GRAPH.edges[p.edgeId];if([e.a,e.b].some(v=>building(s,v)?.owner===pi)){if(p.type==='any')any=true;else sp.add(p.type)}}const o={};RK.forEach(k=>o[k]=sp.has(k)?2:any?3:4);return o}
function computeLongest(s,pi){const own=new Set(GRAPH.edges.filter(e=>road(s,e.id)===pi).map(e=>e.id));if(!own.size)return 0;const blocked=v=>{const b=building(s,v);return b&&b.owner!==pi};function dfs(v,used,arr){let best=used.size;if(arr&&blocked(v))return best;for(const eid of adjE(v)){if(!own.has(eid)||used.has(eid))continue;const e=GRAPH.edges[eid],nv=e.a===v?e.b:e.a,nu=new Set(used);nu.add(eid);best=Math.max(best,dfs(nv,nu,true))}return best}let best=0;for(const v of GRAPH.verts)best=Math.max(best,dfs(v.id,new Set(),false));return best}
function vp(s,pi){let n=0;Object.values(s.buildings||{}).forEach(b=>{if(b.owner===pi)n+=b.level==='city'?2:1});n+=(s.players[pi].devCards||[]).filter(c=>VP_TYPES.has(c.type)).length;if(s.longestRoadHolder===pi)n+=2;if(s.largestArmyHolder===pi)n+=2;return n}

function repairBlockedState(s){
 s.players=ps(s);

 // Never wait for departed players to discard after a 7.
 if(s.pendingDiscards){
   for(const key of Object.keys(s.pendingDiscards)){
     const i=Number(key);
     if(!isActivePlayer(s.players[i]))delete s.pendingDiscards[key];
   }

   if(s.turnPhase==='discard' && Object.keys(s.pendingDiscards).length===0){
     s.turnPhase='moveRobber';
     s.robberResume='postroll';
     s.log=s.log||[];
     s.log.push('🛠️ המשחק שחרר אוטומטית המתנה לשחקן שכבר יצא.');
   }
 }

 // Current turn must always belong to an active player.
 if(s.phase==='playing' && !isActivePlayer(s.players[s.currentPlayer])){
   const next=nextActivePlayer(s,s.currentPlayer);
   if(next!==null){
     s.currentPlayer=next;
     s.turnPhase='preroll';
     s.dice=null;
     delete s.freeRoads;
     delete s.robberVictims;
     delete s.robberResume;
     delete s.pendingDiscards;
     s.tradeOffer=null;
     s.turnCounter=(s.turnCounter||0)+1;
     s.players[next].devPlayed=false;
     s.log=s.log||[];
     s.log.push(`🛠️ התור שוחרר אוטומטית ועבר ל-${s.players[next].name}.`);
   }
 }

 return s
}

function recalc(s){const lens=s.players.map((_,i)=>computeLongest(s,i));s.longestRoadLengths=lens;const m=Math.max(...lens,0),tops=lens.map((x,i)=>x===m?i:-1).filter(i=>i>=0);if(m<5)s.longestRoadHolder=null;else if(tops.length===1)s.longestRoadHolder=tops[0];else if(!tops.includes(s.longestRoadHolder))s.longestRoadHolder=null;const a=s.players.map(p=>p.knightsPlayed||0),am=Math.max(...a,0),at=a.map((x,i)=>x===am?i:-1).filter(i=>i>=0);if(am<3)s.largestArmyHolder=null;else if(at.length===1)s.largestArmyHolder=at[0];else if(!at.includes(s.largestArmyHolder))s.largestArmyHolder=null;s.players.forEach((p,i)=>p.vp=vp(s,i));if(s.phase==='playing'&&s.players[s.currentPlayer]?.vp>=10){s.phase='finished';s.winner=s.currentPlayer;s.log.push(`🏆 ${s.players[s.winner].name} ניצח עם ${s.players[s.winner].vp} נקודות!`)}return s}
function distribute(s,totalRoll){
 const claims=Object.fromEntries(RK.map(k=>[k,[]])),tot=blank();
 let robberBlocked=false;

 for(const[v,b]of Object.entries(s.buildings||{})){
   for(const ti of GRAPH.verts[Number(v)].tiles){
     const t=s.board.tiles[ti];
     if(t.number!==totalRoll||t.resource==='desert')continue;

     // A hex occupied by the robber produces nothing.
     if(ti===s.board.robber){
       robberBlocked=true;
       continue;
     }

     const q=b.level==='city'?2:1;
     claims[t.resource].push({pi:b.owner,q});
     tot[t.resource]+=q;
   }
 }

 for(const k of RK){
   if(tot[k]>0&&s.bank[k]>=tot[k]){
     for(const c of claims[k]){
       s.players[c.pi].resources[k]+=c.q;
       s.bank[k]-=c.q;
     }
   }
 }

 if(robberBlocked){
   s.log=s.log||[];
   s.log.push(`💣 המחבל חסם הפקת משאבים ממשושה מספר ${totalRoll}.`);
 }
}
function randomRes(p){const pool=[];RK.forEach(k=>{for(let i=0;i<(p.resources[k]||0);i++)pool.push(k)});return pool.length?pool[randInt(pool.length)]:null}
function victims(s,pi){const o=new Set();for(const v of GRAPH.tileVerts[s.board.robber]){const b=building(s,v);if(b&&b.owner!==pi&&isActivePlayer(s.players[b.owner])&&total(s.players[b.owner])>0)o.add(b.owner)}return[...o]}
function finishRobber(s,pi){const vs=victims(s,pi);if(vs.length===0){s.turnPhase=s.robberResume||'postroll';delete s.robberResume}else if(vs.length===1){const k=randomRes(s.players[vs[0]]);if(k){const victim=vs[0];s.players[victim].resources[k]--;s.players[pi].resources[k]++;s.log.push(`🎒 ${s.players[pi].name} גנב משאב מ-${s.players[victim].name}.`);s.lastSteal={id:crypto.randomUUID(),thiefId:s.players[pi].id,thiefName:s.players[pi].name,victimId:s.players[victim].id,victimName:s.players[victim].name,ts:Date.now()}}s.turnPhase=s.robberResume||'postroll';delete s.robberResume}else{s.turnPhase='chooseVictim';s.robberVictims=vs}}
async function tx(fn){try{return(await runTransaction(roomRef(code),cur=>{if(!cur)return cur;cur.players=ps(cur);normalizeSpectators(cur);cur.buildings=cur.buildings||{};cur.roads=cur.roads||{};repairBlockedState(cur);return fn(cur)??cur},{applyLocally:false})).snapshot.val()}catch(e){err='הפעולה נכשלה: '+e.message;render()}}
async function createGame(){myName=document.getElementById('name').value.trim();if(!myName)return;localStorage.setItem('myName',myName);let c,x=true;for(let i=0;i<8&&x;i++){c=newCode();x=(await get(roomRef(c))).exists()}code=c;await set(roomRef(code),{code,phase:'lobby',players:[{id:myId,name:myName}],spectators:[],host:myId,log:[]});history.replaceState({},'',`${location.pathname}?room=${code}`);subscribe(code)}
async function joinGame(c){
 myName=document.getElementById('name').value.trim();
 c=clean(c);
 if(!myName||c.length!==4){err='הכנס שם וקוד בן 4 תווים';render();return}
 localStorage.setItem('myName',myName);

 const r=await runTransaction(roomRef(c),cur=>{
   if(!cur)return cur;
   cur.players=ps(cur);
   normalizeSpectators(cur);

   const pi=cur.players.findIndex(p=>p.id===myId);
   const si=cur.spectators.findIndex(p=>p.id===myId);

   // If this browser/device was already a player, restore that exact player.
   if(pi>=0){
     cur.players[pi].name=myName;
     cur.players[pi].left=false;
     if(si>=0)cur.spectators.splice(si,1);
     cur.log=cur.log||[];
     cur.log.push(`↩️ ${myName} חזר למשחק.`);
     return cur
   }

   // New player may join only before start and while there is a free seat.
   if(cur.phase==='lobby' && cur.players.length<4){
     cur.players.push({id:myId,name:myName});
     if(si>=0)cur.spectators.splice(si,1);
     return cur
   }

   // Room full or game already started -> spectator.
   if(si>=0){
     cur.spectators[si].name=myName;
   }else{
     cur.spectators.push({id:myId,name:myName,joinedAt:Date.now()});
     cur.log=cur.log||[];
     cur.log.push(`👀 ${myName} הצטרף כצופה.`);
   }
   return cur
 },{applyLocally:false});

 const s=r.snapshot.val();
 if(!s){err='החדר לא קיים';render();return}

 const playerOk=ps(s).some(p=>p.id===myId);
 const spectatorOk=spectators(s).some(p=>p.id===myId);
 if(!playerOk&&!spectatorOk){err='לא ניתן להצטרף לחדר';render();return}

 code=c;
 history.replaceState({},'',`${location.pathname}?room=${code}`);
 ensureNotificationPermission();
 subscribe(code)
}
async function startGame(){await tx(s=>{
 if(s.host!==myId||s.phase!=='lobby'||s.players.length<2)return s;
 const n=s.players.length;
 const startPlayer=randInt(n);
 const firstRound=Array.from({length:n},(_,i)=>(startPlayer+i)%n);
 const order=[...firstRound,...[...firstRound].reverse()];

 Object.assign(s,{
   phase:'setup',
   board:generateBoard(),
   villageNames:shuffle(GUSH_SETTLEMENT_NAMES),
   nextVillageName:0,
   bank:{wood:19,brick:19,sheep:19,ore:19,wheat:19},
   devDeck:newDevDeck(),
   buildings:{},
   roads:{},
   setupOrder:order,
   setupIndex:0,
   setupMode:'settlement',
   startPlayer,
   currentPlayer:order[0],
   turnPhase:'setup',
   turnCounter:0,
   longestRoadHolder:null,
   largestArmyHolder:null,
   tradeOffer:null
 });
 s.players=s.players.map((p,i)=>({...p,color:PC[i],resources:blank(),devCards:[],knightsPlayed:0,devPlayed:false,vp:0}));
 s.log=[
   '🌱 המשחק התחיל.',
   `🎲 בהגרלה נקבע ש-${s.players[startPlayer].name} מתחיל.`,
   '🧩 המשאבים הוגרלו מחדש בפיזור אקראי ומאוזן.',
   '🏡 שלב ההקמה: מתחילים מהשחקן שהוגרל, ממשיכים לפי הסדר, ובסבב השני הסדר מתהפך.'
 ];
 return s
})}
async function placeVertex(v){const pi=myIndex();if(state.phase==='setup'&&state.currentPlayer===pi&&state.setupMode==='settlement')return tx(s=>{if(!validSettlement(s,v,pi,true))return s;s.buildings[v]={owner:pi,level:'settlement'};if(s.setupIndex>=s.players.length){for(const ti of GRAPH.verts[v].tiles){const t=s.board.tiles[ti];if(t.resource!=='desert'&&s.bank[t.resource]>0){s.bank[t.resource]--;s.players[pi].resources[t.resource]++}}}s.setupPendingVertex=v;s.setupMode='road';s.log.push(`🏡 ${s.players[pi].name} הקים חממה.`);return recalc(s)});if(state.phase==='playing'&&state.currentPlayer===pi&&state.turnPhase==='postroll'&&uiMode==='settlement')return tx(s=>{if(pieceCount(s,pi,'settlement')>=5||!validSettlement(s,v,pi)||!has(s.players[pi],COST.settlement))return s;pay(s,pi,COST.settlement);s.buildings[v]={owner:pi,level:'settlement'};uiMode=null;s.log.push(`🏡 ${s.players[pi].name} הקים חממה.`);return recalc(s)});if(state.phase==='playing'&&state.currentPlayer===pi&&state.turnPhase==='postroll'&&uiMode==='city')return tx(s=>{const b=building(s,v);if(pieceCount(s,pi,'city')>=4||!b||b.owner!==pi||b.level!=='settlement'||!has(s.players[pi],COST.city))return s;pay(s,pi,COST.city);const pool=s.villageNames||GUSH_SETTLEMENT_NAMES,ix=s.nextVillageName||0,villageName=pool[ix%pool.length];s.nextVillageName=ix+1;s.buildings[v]={owner:pi,level:'city',name:villageName};uiMode=null;s.log.push(`🏘️ ${s.players[pi].name} הקים את היישוב ${villageName}.`);return recalc(s)})}
async function placeEdge(eid){const pi=myIndex();if(state.phase==='setup'&&state.currentPlayer===pi&&state.setupMode==='road')return tx(s=>{const e=GRAPH.edges[eid],v=s.setupPendingVertex;if(road(s,eid)!==null||(e.a!==v&&e.b!==v))return s;s.roads[eid]=pi;delete s.setupPendingVertex;s.setupIndex++;if(s.setupIndex>=s.setupOrder.length){s.phase='playing';s.currentPlayer=s.startPlayer??0;s.turnPhase='preroll';s.turnCounter=1;s.log.push(`🎲 שלב ההקמה הסתיים. ${s.players[s.currentPlayer].name}, שהוגרל להתחיל, מקבל את התור הראשון.`)}else{s.currentPlayer=s.setupOrder[s.setupIndex];s.setupMode='settlement'}return recalc(s)});if(state.phase==='playing'&&state.currentPlayer===pi&&uiMode==='road')return tx(s=>{if(pieceCount(s,pi,'road')>=15||!canRoad(s,eid,pi))return s;const free=(s.freeRoads||0)>0;if(!free){if(s.turnPhase!=='postroll'||!has(s.players[pi],COST.road))return s;pay(s,pi,COST.road)}s.roads[eid]=pi;if(free){s.freeRoads--;if(s.freeRoads<=0||pieceCount(s,pi,'road')>=15){delete s.freeRoads;uiMode=null}}else uiMode=null;s.log.push(`🛣️ ${s.players[pi].name} סלל דרך בין מושבים.`);return recalc(s)})}
async function rollDice(){const pi=myIndex();await tx(s=>{if(s.currentPlayer!==pi||s.turnPhase!=='preroll')return s;const a=1+Math.floor(Math.random()*6),b=1+Math.floor(Math.random()*6),t=a+b;s.dice=[a,b];s.log.push(`🎲 ${s.players[pi].name} הטיל ${a}+${b}=${t}.`);if(t===7){s.pendingDiscards={};s.players.forEach((p,i)=>{if(isActivePlayer(p)&&total(p)>7)s.pendingDiscards[i]=Math.floor(total(p)/2)});if(Object.keys(s.pendingDiscards).length){s.turnPhase='discard';s.log.push('📦 יצא 7 - כל שחקן פעיל עם יותר מ-7 משאבים בוחר אילו קלפים להשליך, בכמות של החצי הקטן.')}else{s.turnPhase='moveRobber';s.robberResume='postroll';s.log.push('💣 יצא 7 - אין צורך בהשלכות. יש להזיז את המחבל ולגנוב משאב אקראי משחקן סמוך.')}}else{distribute(s,t);s.turnPhase='postroll'}return s})}
async function submitDiscard(sel){const pi=myIndex();await tx(s=>{const need=s.pendingDiscards?.[pi];if(!need)return s;const sum=RK.reduce((a,k)=>a+(sel[k]||0),0);if(sum!==need)return s;for(const k of RK)if((sel[k]||0)>s.players[pi].resources[k])return s;for(const k of RK){const q=sel[k]||0;s.players[pi].resources[k]-=q;s.bank[k]+=q}s.log.push(`📦 ${s.players[pi].name} השליך ${need} משאבים שבחר.`);delete s.pendingDiscards[pi];if(!Object.keys(s.pendingDiscards).length){s.turnPhase='moveRobber';s.robberResume='postroll';s.log.push(`💣 כל ההשלכות הסתיימו - ${s.players[s.currentPlayer].name} צריך להזיז את המחבל ולגנוב קלף משאב אקראי משחקן סמוך.`)}return s})}
async function moveRobber(ti){const pi=myIndex();await tx(s=>{if(s.currentPlayer!==pi||!['moveRobber','moveRobberDev'].includes(s.turnPhase)||ti===s.board.robber)return s;s.board.robber=ti;s.log.push(`💣 ${s.players[pi].name} העביר את המחבל.`);finishRobber(s,pi);return s})}
async function chooseVictim(v){const pi=myIndex();await tx(s=>{if(s.currentPlayer!==pi||s.turnPhase!=='chooseVictim'||!s.robberVictims.includes(v))return s;const k=randomRes(s.players[v]);if(k){s.players[v].resources[k]--;s.players[pi].resources[k]++;s.log.push(`🎒 ${s.players[pi].name} גנב קלף משאב אקראי מ-${s.players[v].name}.`);s.lastSteal={id:crypto.randomUUID(),thiefId:s.players[pi].id,thiefName:s.players[pi].name,victimId:s.players[v].id,victimName:s.players[v].name,ts:Date.now()}}s.turnPhase=s.robberResume||'postroll';delete s.robberResume;delete s.robberVictims;return s})}
async function endTurn(){const pi=myIndex();await tx(s=>{
 if(s.currentPlayer!==pi||s.turnPhase!=='postroll'||s.freeRoads)return s;
 s.tradeOffer=null;
 s.players[pi].devPlayed=false;
 const next=nextActivePlayer(s,pi);
 if(next===null)return s;
 s.currentPlayer=next;
 s.turnCounter++;
 s.turnPhase='preroll';
 s.dice=null;
 s.log.push(`➡️ תור של ${s.players[next].name}.`);
 return recalc(s)
})}
async function buyDev(){
 const pi=myIndex();
 if(pi<0||isSpectator()){
   alert('צופה אינו יכול לקנות קלפי פיתוח.');
   return;
 }

 let result={ok:false,reason:'unknown',card:null,resources:null};

 try{
   await runTransaction(roomRef(code),s=>{
     if(!s)return s;
     s.players=ps(s);
     normalizeSpectators(s);
     repairBlockedState(s);

     const livePi=s.players.findIndex(p=>p.id===myId);
     if(livePi<0){
       result={ok:false,reason:'not-player'};
       return s
     }

     const p=s.players[livePi];
     p.resources=p.resources||blank();
     p.devCards=Array.isArray(p.devCards)?p.devCards:Object.values(p.devCards||{});
     s.devDeck=Array.isArray(s.devDeck)?s.devDeck:Object.values(s.devDeck||{});

     result.resources={
       sheep:Number(p.resources.sheep||0),
       ore:Number(p.resources.ore||0),
       wheat:Number(p.resources.wheat||0)
     };

     if(s.currentPlayer!==livePi||s.turnPhase!=='postroll'){
       result={...result,ok:false,reason:'turn'};
       return s
     }

     if(!has(p,COST.dev)){
       result={...result,ok:false,reason:'resources'};
       return s
     }

     if(!s.devDeck.length){
       result={...result,ok:false,reason:'empty'};
       return s
     }

     // Preserve all turn-flow fields exactly as they were.
     const keepPhase=s.turnPhase;
     const keepCurrent=s.currentPlayer;
     const keepTurn=s.turnCounter;
     const keepDice=s.dice??null;

     pay(s,livePi,COST.dev);

     const boughtType=s.devDeck.shift();
     p.devCards.push({
       id:crypto.randomUUID(),
       type:boughtType,
       boughtTurn:Number(s.turnCounter||0)
     });

     s.log=s.log||[];
     s.log.push(`🎴 ${p.name} קנה קלף פיתוח.`);

     // Buying a development card must not alter the turn state.
     s.turnPhase=keepPhase;
     s.currentPlayer=keepCurrent;
     s.turnCounter=keepTurn;
     s.dice=keepDice;

     result={ok:true,reason:'ok',card:boughtType};
     return s
   },{applyLocally:false});
 }catch(e){
   console.error('buyDev failed',e);
   alert('הקנייה נכשלה בגלל בעיית תקשורת. נסה שוב.');
   return
 }

 if(result.ok){
   const cardName=DEV_NAMES?.[result.card]||'קלף פיתוח';
   alert(`קנית קלף פיתוח: ${cardName}\n\nאפשר להמשיך את התור כרגיל.`);
   verifyTurnAfterAction();
   return
 }

 if(result.reason==='turn'){
   alert('אפשר לקנות קלף פיתוח רק בתורך, אחרי הטלת הקוביות.');
 }else if(result.reason==='resources'){
   const r=result.resources||{sheep:0,ore:0,wheat:0};
   alert(
     'אין לך מספיק משאבים.\n' +
     'עלות: 🥬1 + 🌱1 + 🍅1\n\n' +
     `אצלך כרגע: 🥬${r.sheep} + 🌱${r.ore} + 🍅${r.wheat}`
   );
 }else if(result.reason==='empty'){
   alert('נגמרו קלפי הפיתוח בחפיסה.');
 }else{
   alert('לא ניתן לקנות כרגע קלף פיתוח.');
 }
}
function playable(p){return(p.devCards||[]).filter(c=>!VP_TYPES.has(c.type)&&c.boughtTurn<state.turnCounter)}
async function playDev(id){const pi=myIndex(),card=state.players[pi].devCards.find(c=>c.id===id);if(!card)return;if(card.type==='yearPlenty'){modal={type:'year',id};renderModal();return}if(card.type==='monopoly'){modal={type:'mono',id};renderModal();return}await tx(s=>{const p=s.players[pi],c=p.devCards.find(x=>x.id===id);if(s.currentPlayer!==pi||p.devPlayed||!c||c.boughtTurn>=s.turnCounter)return s;if(c.type==='knight'){p.devCards=p.devCards.filter(x=>x.id!==id);p.devPlayed=true;p.knightsPlayed++;s.robberResume=s.turnPhase;s.turnPhase='moveRobberDev';s.log.push(`💣 ${p.name} הפעיל קלף מחבל.`)}else if(c.type==='roadBuilding'){p.devCards=p.devCards.filter(x=>x.id!==id);p.devPlayed=true;s.freeRoads=2;uiMode='road';s.log.push(`🛣️ ${p.name} הפעיל פריצת דרך.`)}return recalc(s)})}
async function year(id,a,b){const pi=myIndex();await tx(s=>{const p=s.players[pi],c=p.devCards.find(x=>x.id===id);if(s.currentPlayer!==pi||p.devPlayed||!c||c.boughtTurn>=s.turnCounter)return s;const need=blank();need[a]++;need[b]++;if(RK.some(k=>s.bank[k]<need[k]))return s;RK.forEach(k=>{if(need[k])takeBank(s,pi,k,need[k])});p.devCards=p.devCards.filter(x=>x.id!==id);p.devPlayed=true;return recalc(s)});closeModal()}
async function monopoly(id,k){const pi=myIndex();await tx(s=>{const p=s.players[pi],c=p.devCards.find(x=>x.id===id);if(s.currentPlayer!==pi||p.devPlayed||!c||c.boughtTurn>=s.turnCounter)return s;let n=0;s.players.forEach((x,i)=>{if(i!==pi){n+=x.resources[k];x.resources[k]=0}});p.resources[k]+=n;p.devCards=p.devCards.filter(x=>x.id!==id);p.devPlayed=true;s.log.push(`📣 ${p.name} הפעיל שיווק מרוכז וקיבל ${n} ${R[k].name}.`);return recalc(s)});closeModal()}
async function bankTrade(g,t){
 const pi=myIndex();
 let result='unknown',rate=4;
 await tx(s=>{
   if(s.currentPlayer!==pi||s.turnPhase!=='postroll'){result='turn';return s}
   if(g===t){result='same';return s}
   rate=portRates(s,pi)[g];
   if(Number(s.players[pi].resources[g]||0)<rate){result='resources';return s}
   if(Number(s.bank[t]||0)<1){result='bank';return s}
   s.players[pi].resources[g]-=rate;
   s.bank[g]+=rate;
   s.bank[t]--;
   s.players[pi].resources[t]++;
   s.log=s.log||[];
   s.log.push(`⚓ ${s.players[pi].name} ביצע מסחר עם הבנק.`);
   result='ok';
   return s
 });
 if(result==='ok')closeModal();
 else if(result==='resources')alert(`אין לך מספיק ${R[g].name}. צריך ${rate} קלפים למסחר הזה.`);
 else if(result==='bank')alert(`אין כרגע ${R[t].name} בבנק.`);
 else if(result==='same')alert('בחר משאב שונה לקבלה.');
 else if(result==='turn')alert('אפשר לסחור עם הבנק רק בתורך, אחרי הטלת הקוביות.');
}
async function makeTrade(g,w){
 const pi=myIndex();
 let result='unknown';
 await tx(s=>{
   if(s.currentPlayer!==pi||s.turnPhase!=='postroll'){result='turn';return s}
   const gs=RK.reduce((a,k)=>a+Number(g[k]||0),0);
   const ws=RK.reduce((a,k)=>a+Number(w[k]||0),0);
   if(!gs||!ws){result='empty';return s}
   for(const k of RK){
     if(Number(g[k]||0)>Number(s.players[pi].resources[k]||0)){result='resources';return s}
   }
   s.tradeOffer={from:pi,give:g,want:w,rejectedBy:[]};
   s.log=s.log||[];
   s.log.push(`🤝 ${s.players[pi].name} הציע עסקה.`);
   result='ok';
   return s
 });
 if(result==='ok')closeModal();
 else if(result==='turn')alert('אפשר להציע עסקה רק בתורך, אחרי הטלת הקוביות.');
 else if(result==='empty')alert('צריך לבחור לפחות משאב אחד שאתה נותן ומשאב אחד שאתה מבקש.');
 else if(result==='resources')alert('ניסית להציע יותר משאבים ממה שיש לך.');
}
async function acceptTrade(){const pi=myIndex();await tx(s=>{const o=s.tradeOffer;if(!o||o.from===pi)return s;for(const k of RK)if(s.players[o.from].resources[k]<o.give[k]||s.players[pi].resources[k]<o.want[k])return s;for(const k of RK){s.players[o.from].resources[k]-=o.give[k];s.players[pi].resources[k]+=o.give[k];s.players[pi].resources[k]-=o.want[k];s.players[o.from].resources[k]+=o.want[k]}s.tradeOffer=null;return s})}

async function rejectTrade(){
 const pi=myIndex();
 await tx(s=>{
   const o=s.tradeOffer;
   if(!o||o.from===pi)return s;
   o.rejectedBy=Array.isArray(o.rejectedBy)?o.rejectedBy:[];
   if(!o.rejectedBy.includes(pi)){
     o.rejectedBy.push(pi);
     s.log=s.log||[];
     s.log.push(`❌ ${s.players[pi].name} סירב לעסקה של ${s.players[o.from].name}.`);
   }
   const others=s.players.map((p,i)=>isActivePlayer(p)&&i!==o.from?i:-1).filter(i=>i>=0);
   if(others.every(i=>o.rejectedBy.includes(i))){
     s.log.push(`🚫 כל השחקנים סירבו לעסקה של ${s.players[o.from].name}. העסקה נסגרה.`);
     s.tradeOffer=null;
   }else{
     s.tradeOffer=o;
   }
   return s
 })
}



async function verifyTurnAfterAction(){
 if(!code||!state)return;
 try{
   const snap=await get(roomRef(code));
   const s=snap.val();
   if(!s)return;
   const players=ps(s);
   const cur=players[s.currentPlayer];
   if(s.phase==='playing' && (!cur || cur.left)){
     await runTransaction(roomRef(code),x=>{
       if(!x)return x;
       x.players=ps(x);
       normalizeSpectators(x);
       return repairBlockedState(x)
     },{applyLocally:false});
   }
 }catch(e){
   console.warn('Turn verification failed',e)
 }
}

async function rescueStuckTurn(){
 if(!state||state.host!==myId)return;
 const cur=state.players?.[state.currentPlayer];
 const label=cur?.name||'השחקן הנוכחי';

 if(!confirm(`לנסות לשחרר את המצב התקוע בתור של ${label}?`))return;

 await runTransaction(roomRef(code),s=>{
   if(!s)return s;
   s.players=ps(s);
   normalizeSpectators(s);

   const beforePhase=s.turnPhase;
   const beforePlayer=s.currentPlayer;

   repairBlockedState(s);

   // If automatic repair found nothing, force a safe pass to next active player.
   if(beforePhase===s.turnPhase && beforePlayer===s.currentPlayer){
     const next=nextActivePlayer(s,s.currentPlayer);
     if(next!==null){
       s.tradeOffer=null;
       delete s.freeRoads;
       delete s.pendingDiscards;
       delete s.robberResume;
       delete s.robberVictims;
       s.currentPlayer=next;
       s.turnPhase='preroll';
       s.dice=null;
       s.turnCounter=(s.turnCounter||0)+1;
       s.players[next].devPlayed=false;
       s.log=s.log||[];
       s.log.push(`🛠️ המארח שחרר ידנית את התור. התור עבר ל-${s.players[next].name}.`);
     }
   }

   return recalc(s)
 },{applyLocally:false})
}
async function cancelTrade(){const pi=myIndex();await tx(s=>{if(s.tradeOffer?.from===pi)s.tradeOffer=null;return s})}
function fmt(b){return RK.filter(k=>(b?.[k]||0)>0).map(k=>`${b[k]} ${R[k].icon}`).join(' + ')||'-'}
function ratesText(s,pi){const x=portRates(s,pi);return RK.map(k=>`${R[k].icon}${x[k]}:1`).join(' · ')}
function devSummary(p){const g={};for(const c of p.devCards||[])g[DEV_NAMES[c.type]]=(g[DEV_NAMES[c.type]]||0)+1;return Object.entries(g).map(([n,q])=>`${n} ×${q}`).join(' · ')||'אין'}
function hex(cx,cy,r){const a=[];for(let i=0;i<6;i++){const t=(60*i-30)*Math.PI/180;a.push(`${(cx+r*Math.cos(t)).toFixed(1)},${(cy+r*Math.sin(t)).toFixed(1)}`)}return a.join(' ')}
function renderBoard(){if(!state?.board)return'';const pi=myIndex(),setupS=state.phase==='setup'&&state.currentPlayer===pi&&state.setupMode==='settlement',setupR=state.phase==='setup'&&state.currentPlayer===pi&&state.setupMode==='road',canV=setupS||uiMode==='settlement'||uiMode==='city',canE=setupR||uiMode==='road',rob=['moveRobber','moveRobberDev'].includes(state.turnPhase)&&state.currentPlayer===pi;let z=`<svg class="board-svg" viewBox="0 0 610 510" style="width:100%;max-width:830px;height:auto"><rect width="610" height="510" rx="24" fill="#287cad"/>`;state.board.tiles.forEach((t,i)=>{const[cx,cy]=CENTERS[i],inf=R[t.resource];z+=`<g class="${rob?'tilehit':''}" ${rob?`onclick="window.moveRobberClick(${i})"`:''}><polygon class="hex" points="${hex(cx,cy,HEXR)}" fill="${inf.color}" stroke="#f4ead5" stroke-width="2"/><text x="${cx}" y="${cy-15}" text-anchor="middle" font-size="23">${inf.icon}</text><text x="${cx}" y="${cy+5}" text-anchor="middle" font-size="12" font-weight="800" fill="#20303a">${inf.name}</text>`;if(t.number)z+=`<circle cx="${cx}" cy="${cy+28}" r="16" fill="${[6,8].includes(t.number)?'#fff0f0':'#fbf7ed'}" stroke="#6e5431" stroke-width="2"/><text x="${cx}" y="${cy+34}" text-anchor="middle" font-size="17" font-weight="900" fill="#322416">${t.number}</text>`;else z+=`<text x="${cx}" y="${cy+31}" text-anchor="middle" font-size="12" font-weight="900" fill="#523b1e">דיונה</text>`;if(state.board.robber===i)z+=`<circle cx="${cx+29}" cy="${cy-33}" r="13" fill="#1d1d1d" stroke="#fff"/><text x="${cx+29}" y="${cy-28}" text-anchor="middle" font-size="16">💣</text>`;z+='</g>'});for(const p of state.board.ports){const e=GRAPH.edges[p.edgeId],a=GRAPH.verts[e.a],b=GRAPH.verts[e.b],mx=(a.x+b.x)/2,my=(a.y+b.y)/2,dx=mx-305,dy=my-248,l=Math.hypot(dx,dy)||1,x=mx+dx/l*28,y=my+dy/l*28;z+=`<circle cx="${x}" cy="${y}" r="17" fill="#f7ecd2" stroke="#654c2d"/><text x="${x}" y="${y+4}" text-anchor="middle" font-size="10" font-weight="900" fill="#3d2a17">${p.type==='any'?'3:1':R[p.type].icon+'2:1'}</text>`}for(const[eid,o]of Object.entries(state.roads||{})){const e=GRAPH.edges[+eid],a=GRAPH.verts[e.a],b=GRAPH.verts[e.b];z+=`<line x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}" stroke="${state.players[o].color}" stroke-width="8" stroke-linecap="round"/><line x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}" stroke="#fff" stroke-width="2" opacity=".5"/>`}for(const[vid,b]of Object.entries(state.buildings||{})){const v=GRAPH.verts[+vid],c=state.players[b.owner].color;if(b.level==='settlement')z+=`<g transform="translate(${v.x-8},${v.y-8})"><rect x="1" y="5" width="14" height="10" rx="2" fill="${c}" stroke="#fff"/><path d="M1 6 L8 0 L15 6" fill="${c}" stroke="#fff"/></g>`;else z+=`<g transform="translate(${v.x-12},${v.y-12})"><rect x="0" y="9" width="10" height="10" rx="2" fill="${c}" stroke="#fff" stroke-width="1.2"/><path d="M0 10 L5 4 L10 10" fill="${c}" stroke="#fff" stroke-width="1.2"/><rect x="2.8" y="13" width="3" height="6" fill="#f5d99d"/><rect x="8" y="6" width="12" height="14" rx="2" fill="${c}" stroke="#fff" stroke-width="1.4"/><path d="M8 7 L14 0 L20 7" fill="${c}" stroke="#fff" stroke-width="1.4"/><rect x="11" y="11" width="3" height="3" fill="#f5d99d"/><rect x="15" y="11" width="3" height="3" fill="#f5d99d"/><rect x="13" y="15" width="3.5" height="5" fill="#f5d99d"/></g>${b.name?`<g class="village-label"><rect x="${v.x+14}" y="${v.y-19}" width="${Math.max(42,b.name.length*6.2+10)}" height="17" rx="7" fill="rgba(8,29,49,.92)" stroke="${c}" stroke-width="1"/><text x="${v.x+19}" y="${v.y-7}" font-size="9.5" font-weight="800" fill="#fff">${b.name}</text></g>`:''}`}if(canE)GRAPH.edges.forEach(e=>{const a=GRAPH.verts[e.a],b=GRAPH.verts[e.b],ok=setupR?(state.setupPendingVertex===e.a||state.setupPendingVertex===e.b)&&road(state,e.id)===null:canRoad(state,e.id,pi);if(ok)z+=`<line class="edgehit" onclick="window.edgeClick(${e.id})" x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}" stroke="rgba(255,255,255,.12)" stroke-width="15" stroke-linecap="round"/>`});if(canV)GRAPH.verts.forEach(v=>{const ok=uiMode==='city'?(building(state,v.id)?.owner===pi&&building(state,v.id)?.level==='settlement'):validSettlement(state,v.id,pi,setupS);if(ok)z+=`<circle class="vertexhit" onclick="window.vertexClick(${v.id})" cx="${v.x}" cy="${v.y}" r="10" fill="rgba(255,255,255,.17)" stroke="#ffd166" stroke-width="2"/>`});return z+'</svg>'}
function hint(){const pi=myIndex();if(state.phase==='setup')return state.currentPlayer!==pi?`שלב ההקמה - ממתין ל-${state.players[state.currentPlayer].name}`:state.setupMode==='settlement'?'בחר צומת להקמת חממה':'בחר דרך צמודה לחממה';if(state.phase==='finished')return`🏆 ${state.players[state.winner].name} ניצח`;if(state.turnPhase==='discard')return state.pendingDiscards?.[pi]?`עליך להשליך ${state.pendingDiscards[pi]} משאבים`:'ממתינים להשלכת משאבים';if(['moveRobber','moveRobberDev'].includes(state.turnPhase)&&state.currentPlayer===pi)return'בחר משושה חדש למחבל';if(state.turnPhase==='chooseVictim'&&state.currentPlayer===pi)return'בחר שחקן לגניבה';if(uiMode==='road')return state.freeRoads?`בחר דרך - נשארו ${state.freeRoads} חינם`:'בחר דרך לבנייה';if(uiMode==='settlement')return'בחר מקום לחממה';if(uiMode==='city')return'בחר חממה לשדרוג ליישוב';return''}
function home(){return`<div class="page"><div class="card"><div style="font-size:46px">🌱</div><div class="title">המתיישבים - גרסת הגוש</div><div class="sub">משחק מלא מרובה משתתפים</div>${ferr?`<div class="err">${ferr}</div>`:`<div class="notice">${ready?'✅ מחובר ל-Firebase':'⏳ מתחבר'}</div>`}${err?`<div class="err">${err}</div>`:''}<input id="name" class="field" placeholder="השם שלך" value="${myName}"><div style="height:10px"></div><button id="create" class="btn primary" style="width:100%">צור משחק חדש</button><div style="height:10px"></div><div class="row"><input id="room" class="field" maxlength="4" placeholder="קוד" value="${code}" style="text-align:center;letter-spacing:4px;font-weight:900"><button id="join" class="btn green" style="flex:0 0 105px">הצטרף</button></div></div></div>`}
function lobby(){const p=ps(),sp=spectators(),host=state.host===myId;return`<div class="page"><div class="card"><div class="notice">✅ החדר מסונכרן בזמן אמת</div><div class="title" style="font-size:26px">ממתינים לשחקנים</div><div style="background:#fff;border:2px dashed #d6c6a9;border-radius:14px;padding:14px;text-align:center;margin:14px 0"><div class="muted">קוד החדר</div><div style="font-size:38px;letter-spacing:7px;font-weight:900;color:#2563eb">${code}</div><button id="copy" class="btn orange" style="margin-top:8px">העתק קישור</button></div><div class="plist">${p.map((x,i)=>`<div class="pitem" style="background:#f6f1e8"><div class="dot" style="background:${PC[i]}"></div><div>${x.name}${x.left?' <span class="badge">יצא</span>':''}</div><div>${x.id===state.host?'<span class="badge" style="color:#555">מארח</span>':''}${x.id===myId?'<span class="badge" style="color:#2457ad">אתה</span>':''}</div></div>`).join('')}</div>${sp.length?`<div class="spectator-block"><div class="muted">👀 צופים (${sp.length})</div>${sp.map(x=>`<div class="spectator-row">${x.name}${x.id===myId?' <b>(אתה)</b>':''}</div>`).join('')}</div>`:''}<div style="height:12px"></div>${host&&p.filter(x=>!x.left).length>=2?'<button id="start" class="btn primary" style="width:100%">התחל משחק</button>':`<div class="muted">${host?'צריך לפחות 2 שחקנים':'ממתין למארח'}</div>`}<button id="leave" class="btn ghost" style="margin-top:10px">חזרה</button></div></div>`}

function closeModal(){modal=null;const root=document.getElementById('modalRoot');if(root)root.innerHTML=''}
function opts(){return RK.map(k=>`<option value="${k}">${R[k].icon} ${R[k].name}</option>`).join('')}
function inputs(prefix,max={}){
 return `<div class="resinputs">${RK.map(k=>`<label><span>${R[k].icon} ${R[k].name}</span><input id="${prefix}_${k}" type="number" min="0" max="${max[k]??99}" value="0"></label>`).join('')}</div>`
}
function renderModal(){
 const root=document.getElementById('modalRoot');
 if(!root||!modal)return;
 const pi=myIndex();
 const me=pi>=0?state.players[pi]:null;
 let b='';

 if(modal.type==='discard'){
   b=`<h3>יצא 7 - השלכת משאבים</h3>
   <div style="margin-bottom:8px">יש לך יותר מ-7 קלפי משאב. עליך לבחור בעצמך אילו קלפים להשליך.</div>
   <div>יש להשליך בדיוק <b>${modal.need}</b> קלפים.</div>
   ${inputs('d',me?.resources||{})}
   <div class="modalactions"><button class="btn red" id="dok">השלך את הקלפים שבחרתי</button></div>`
 }

 if(modal.type==='bank'){
   b=`<h3>מסחר עם הבנק</h3>
   <div class="mrow"><label>נותן</label><select id="bg">${opts()}</select></div>
   <div class="mrow"><label>מקבל</label><select id="bt">${opts()}</select></div>
   <div class="tiny" style="margin-top:8px">המשחק ישתמש אוטומטית בשער המסחר הטוב ביותר שלך.</div>
   <div class="modalactions"><button class="btn green" id="bok">בצע עסקה</button><button class="btn ghost" id="close">סגור</button></div>`
 }

 if(modal.type==='trade'){
   b=`<h3>הצע עסקה לשחקנים</h3>
   <b>אני נותן</b>
   ${inputs('g',me?.resources||{})}
   <b>אני מבקש</b>
   ${inputs('w')}
   <div class="modalactions"><button class="btn green" id="tok">פרסם עסקה</button><button class="btn ghost" id="close">סגור</button></div>`
 }

 if(modal.type==='year'){
   b=`<h3>יבול מבורך</h3>
   <div class="mrow"><label>משאב 1</label><select id="y1">${opts()}</select></div>
   <div class="mrow"><label>משאב 2</label><select id="y2">${opts()}</select></div>
   <div class="modalactions"><button class="btn green" id="yok">קח</button><button class="btn ghost" id="close">סגור</button></div>`
 }

 if(modal.type==='mono'){
   b=`<h3>שיווק מרוכז</h3>
   <div class="mrow"><label>משאב</label><select id="mo">${opts()}</select></div>
   <div class="modalactions"><button class="btn green" id="mok">הפעל</button><button class="btn ghost" id="close">סגור</button></div>`
 }

 root.innerHTML=`<div class="modalback"><div class="modal">${b}</div></div>`;
 const q=id=>document.getElementById(id);

 if(q('close'))q('close').onclick=closeModal;
 if(q('dok'))q('dok').onclick=()=>{
   const sel={};RK.forEach(k=>sel[k]=+q('d_'+k).value||0);
   submitDiscard(sel).then(()=>{closeModal();render()})
 };
 if(q('bok'))q('bok').onclick=()=>bankTrade(q('bg').value,q('bt').value);
 if(q('tok'))q('tok').onclick=()=>{
   const g={},w={};
   RK.forEach(k=>{g[k]=+q('g_'+k).value||0;w[k]=+q('w_'+k).value||0});
   makeTrade(g,w)
 };
 if(q('yok'))q('yok').onclick=()=>year(modal.id,q('y1').value,q('y2').value);
 if(q('mok'))q('mok').onclick=()=>monopoly(modal.id,q('mo').value)
}

function escChat(s){return String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
function chatMessages(s=state){return Array.isArray(s?.chat)?s.chat:Object.values(s?.chat||{})}
async function sendChat(){
 const input=document.getElementById('chatInput'); if(!input)return;
 const text=(input.value||'').trim().slice(0,300); if(!text)return;
 const pi=myIndex(); if(pi<0)return;
 input.value='';
 await tx(s=>{
   const list=chatMessages(s);
   list.push({id:crypto.randomUUID(),playerId:myId,playerIndex:pi,name:s.players[pi]?.name||myName,text,ts:Date.now()});
   s.chat=list.slice(-60);
   return s
 })
}
function chatHtml(){
 const msgs=chatMessages();
 if(!msgs.length)return '<div class="chatempty">עדיין אין הודעות. כתוב משהו לשחקנים.</div>';
 return msgs.slice(-40).map(m=>{
   if(m.system){
     return `<div class="chatmsg system"><div class="chatbubble">ℹ️ ${escChat(m.text)}</div></div>`
   }
   const mine=m.playerId===myId;
   const color=state.players?.[m.playerIndex]?.color||'#9db4ca';
   return `<div class="chatmsg ${mine?'mine':''}">
     <div class="chatmeta"><span class="dot" style="background:${color}"></span><b>${escChat(m.name)}</b></div>
     <div class="chatbubble">${escChat(m.text)}</div>
   </div>`
 }).join('')
}

function game(){const pi=myIndex(),watching=pi<0||isSpectator(),me=pi>=0?state.players[pi]:{resources:blank(),devCards:[],vp:0,knightsPlayed:0},cur=state.players[state.currentPlayer],mine=!watching&&state.currentPlayer===pi,post=state.phase==='playing'&&mine&&state.turnPhase==='postroll',offer=state.tradeOffer;return`<div class="shell"><div class="topbar"><div class="brand"><div class="brandico">🌱</div>המתיישבים - גרסת הגוש</div><div class="meta"><span class="pill">חדר ${code}</span><span class="pill">תור: <b style="color:${cur?.color}">${cur?.name||'-'}</b></span>${watching?'<span class="pill spectator-pill">👀 מצב צופה</span>':`<span class="pill">נקודות: <b>${me?.vp||0}</b>/10</span>`}${state.dice?`<span class="pill dicepill">🎲 יצא <b>${state.dice[0]+state.dice[1]}</b> <span class="tiny">(${state.dice[0]}+${state.dice[1]})</span></span>`:''}</div></div><div class="layout"><div class="panel"><div class="sec"><div class="sect">התור</div><div class="turnbox"><div class="muted">${mine?'התור שלך':'השחקן הפעיל'}</div><div class="turnname" style="color:${cur?.color}">${mine?'אתה':cur?.name}</div>${state.dice?`<div class="dicebig"><div class="dicetotal">${state.dice[0]+state.dice[1]}</div><div class="diceparts">🎲 ${state.dice[0]} + ${state.dice[1]}</div></div>`:''}${mine&&state.turnPhase==='preroll'?'<button id="roll" class="big red">🎲 הטל קוביות</button>':''}${mine&&state.turnPhase==='postroll'?'<button id="end" class="big orange">סיים תור</button>':''}${state.phase==='finished'?`<div style="font-size:20px;font-weight:900">🏆 ${state.players[state.winner].name} ניצח!</div>`:''}</div></div><div class="sec"><div class="sect">${watching?'👀 מצב צופה':'המשאבים שלי'}</div>${watching?'<div class="notice spectator-notice">אתה צופה במשחק. הפעולות חסומות.</div>':''}<div class="resgrid">${RK.map(k=>`<div class="res"><span>${R[k].icon} ${R[k].name}</span><span class="resn">${me?.resources?.[k]||0}</span></div>`).join('')}</div>${watching?'':`<div class="tiny" style="margin-top:8px">שערי מסחר: ${ratesText(state,pi)}</div>`}</div><div class="sec"><div class="sect">פעולות</div><div class="actiongrid"><button class="actionbtn ${uiMode==='road'?'active':''}" id="road" ${!post&&!state.freeRoads?'disabled':''}>🛣️ דרך<br><span class="tiny">🌸1 + 🏖️1</span></button><button class="actionbtn ${uiMode==='settlement'?'active':''}" id="settle" ${!post?'disabled':''}>🏡 חממה<br><span class="tiny">🌸1 🏖️1 🥬1 🍅1</span></button><button class="actionbtn ${uiMode==='city'?'active':''}" id="city" ${!post?'disabled':''}>🏘️ יישוב<br><span class="tiny">🌱3 + 🍅2</span></button><button class="actionbtn devbuybtn" id="buydev" ${!post?'disabled':''}>🎴 קנה קלף פיתוח<br><span class="tiny">עלות: 🥬1 + 🌱1 + 🍅1 · בחפיסה: ${state.devDeck?.length ?? 0}</span></button><button class="actionbtn" id="banktrade" ${!post?'disabled':''}>⚓ מסחר עם הבנק</button><button class="actionbtn" id="ptrade" ${!post||offer?'disabled':''}>🤝 הצע עסקה</button>${state.freeRoads?'<button class="actionbtn full" id="skipfree">סיים פריצת דרך</button>':''}</div></div><div class="sec"><div class="sect">קלפי הפיתוח שלי</div>
<div class="muted">${devSummary(me)}</div>
<div style="height:7px"></div>
${(Array.isArray(me.devCards)?me.devCards:Object.values(me.devCards||{})).map(c=>VP.has(c.type)
  ? `<div class="devcardrow"><span>🏆 ${DEV_NAMES[c.type]||c.type||'קלף פיתוח'}</span><span class="badge">נקודת ניצחון</span></div>`
  : c.boughtTurn>=state.turnCounter
    ? `<div class="devcardrow"><span>🎴 ${DEV_NAMES[c.type]||c.type||'קלף פיתוח'}</span><span class="badge">חדש - מהתור הזה</span></div>`
    : `<button class="actionbtn full" onclick="window.playDevClick('${c.id}')" ${(!mine||me.devPlayed||state.phase!=='playing')?'disabled':''}>הפעל: ${DEV_NAMES[c.type]||c.type||'קלף פיתוח'}</button>`
).join('')||'<div class="tiny">אין לך עדיין קלפי פיתוח.</div>'}
</div><div class="sec"><div class="sect">שחקנים</div><div class="plist">${state.players.map((p,i)=>`<div class="pitem"><div class="dot" style="background:${p.color}"></div><div><b style="${p.left?'opacity:.55;text-decoration:line-through':''}">${p.name}</b>${p.left?'<span class="left-badge">יצא</span>':''}<div class="tiny">${p.vp||0} נק' · 🃏 ${total(p)} קלפים · מחבלים: ${p.knightsPlayed||0} · דרך: ${state.longestRoadLengths?.[i]||0}</div></div><div class="player-public-info"><span class="cardcount">${total(p)} 🃏</span><span>${i===state.longestRoadHolder?'🛣️':''}${i===state.largestArmyHolder?'🛡️':''}</span></div></div>`).join('')}</div>${spectators().length?`<div class="sec"><div class="sect">👀 צופים</div><div class="spectator-game-list">${spectators().map(x=>`<span class="spectator-chip">${x.name}${x.id===myId?' (אתה)':''}</span>`).join('')}</div></div>`:''}</div></div><div class="center"><div class="boardhead"><div><b>הלוח</b><div class="tiny">חממה = יישוב, יישוב = עיר, דרך בין מושבים = כביש</div></div><div class="legend">${RK.map(k=>`<span class="leg">${R[k].icon} ${R[k].name}</span>`).join('')}</div></div><div class="boardwrap">${renderBoard()}</div><div class="hint">${hint()}</div></div><div class="panel right">${offer?`<div class="sec"><div class="sect">עסקה פתוחה</div><div class="offer"><b>${state.players[offer.from].name}</b> נותן ${fmt(offer.give)}<br>ומבקש ${fmt(offer.want)}<div style="height:8px"></div>${watching?'<div class="tiny">👀 צופה אינו יכול להשתתף בעסקה.</div>':offer.from===pi
?'<button id="canceltrade" class="btn red" style="width:100%">בטל עסקה</button>'
:(offer.rejectedBy||[]).includes(pi)
?'<div class="muted" style="text-align:center">❌ סירבת לעסקה הזו</div>'
:'<div class="row"><button id="accepttrade" class="btn green">קבל</button><button id="rejecttrade" class="btn red">סרב</button></div>'}</div></div>`:''}${state.turnPhase==='chooseVictim'&&mine?`<div class="sec"><div class="sect">בחר שחקן לגניבה</div>${state.robberVictims.map(v=>`<button class="actionbtn full" onclick="window.victimClick(${v})">${state.players[v].name}</button>`).join('')}</div>`:''}<div class="sec chatsec"><div class="sect">💬 צ'אט משחק</div><div id="chatList" class="chatlist">${chatHtml()}</div><div class="chatcomposer"><input id="chatInput" maxlength="300" placeholder="כתוב הודעה..." autocomplete="off"><button id="chatSend" class="btn primary">שלח</button></div></div><div class="sec"><div class="sect">🏘️ יישובי הגוש שהוקמו</div><div class="village-list">${Object.values(state.buildings||{}).filter(b=>b.level==='city'&&b.name).map(b=>`<div class="village-row"><span class="dot" style="background:${state.players[b.owner]?.color||'#fff'}"></span><b>${b.name}</b><span class="tiny">${state.players[b.owner]?.name||''}</span></div>`).join('')||'<div class="tiny">עדיין לא הוקמו יישובים.</div>'}</div></div><div class="sec"><div class="sect">בונוסים</div><div class="linecard">🛡️ מערך השמירה הגדול ביותר - 2 נקודות, החל מ-3 קלפי מחבל.</div><div class="linecard">🛣️ דרך ההתיישבות הארוכה ביותר - 2 נקודות, החל מאורך 5.</div></div><div class="sec"><div class="sect">יומן</div><div class="log">${(state.log||[]).slice(-16).reverse().map(x=>`<div class="logline">${x}</div>`).join('')}</div></div><div class="sec">${state.host===myId&&state.phase==='playing'?'<button id="rescueturn" class="btn rescue-btn" style="width:100%;margin-bottom:7px">🛠️ שחרר תור תקוע</button>':''}<button id="copy2" class="btn green" style="width:100%">העתק קישור לחדר</button><button id="leave2" class="btn ghost" style="width:100%;margin-top:7px">יציאה</button></div></div></div></div>`}
function render(){document.getElementById('app').innerHTML=screen==='home'?home():screen==='lobby'?lobby():game();bind();const pi=myIndex();if(state?.turnPhase==='discard'&&state.pendingDiscards?.[pi]&&!modal){modal={type:'discard',need:state.pendingDiscards[pi]};renderModal()}}
function bind(){const q=id=>document.getElementById(id);if(screen==='home'){q('create').onclick=createGame;q('join').onclick=()=>joinGame(q('room').value)}else if(screen==='lobby'){q('copy').onclick=copyLink;q('leave').onclick=leave;if(q('start'))q('start').onclick=startGame}else{if(q('roll'))q('roll').onclick=rollDice;if(q('end'))q('end').onclick=endTurn;if(q('road'))q('road').onclick=()=>{
 const pi=myIndex();
 if(uiMode==='road'){uiMode=null;render();return}
 if(!state.freeRoads){
   const p=state.players?.[pi];
   if(!p||!has(p,COST.road)){
     const flowers=Number(p?.resources?.wood||0);
     const sand=Number(p?.resources?.brick||0);
     alert(`אין מספיק משאבים לדרך.\nעלות: 🌸1 + 🏖️1\nאצלך: 🌸${flowers} + 🏖️${sand}`);
     return
   }
 }
 uiMode='road';
 render()
};if(q('settle'))q('settle').onclick=()=>{uiMode=uiMode==='settlement'?null:'settlement';render()};if(q('city'))q('city').onclick=()=>{uiMode=uiMode==='city'?null:'city';render()};if(q('buydev'))q('buydev').onclick=buyDev;if(q('skipfree'))q('skipfree').onclick=()=>tx(s=>{if(s.currentPlayer===myIndex()){delete s.freeRoads;uiMode=null}return s});if(q('banktrade'))q('banktrade').onclick=()=>{modal={type:'bank'};renderModal()};if(q('ptrade'))q('ptrade').onclick=()=>{modal={type:'trade'};renderModal()};if(q('accepttrade'))q('accepttrade').onclick=acceptTrade;if(q('rejecttrade'))q('rejecttrade').onclick=rejectTrade;if(q('canceltrade'))q('canceltrade').onclick=cancelTrade;if(q('chatSend'))q('chatSend').onclick=sendChat;if(q('chatInput'))q('chatInput').onkeydown=e=>{if(e.key==='Enter'&&!e.shiftKey){e.preventDefault();sendChat()}};if(q('rescueturn'))q('rescueturn').onclick=rescueStuckTurn;q('copy2').onclick=copyLink;q('leave2').onclick=leave;setTimeout(()=>{const c=q('chatList');if(c)c.scrollTop=c.scrollHeight},0)}}
function copyLink(){const u=`${location.origin}${location.pathname}?room=${code}`;navigator.clipboard?.writeText(u).then(()=>alert('הקישור הועתק')).catch(()=>prompt('העתק:',u))}
async function leave(){
 const leavingCode=code,leavingName=myName,leavingId=myId;

 if(ready&&leavingCode&&state){
   try{
     await runTransaction(roomRef(leavingCode),s=>{
       if(!s)return s;
       s.players=ps(s);
       normalizeSpectators(s);

       const idx=s.players.findIndex(p=>p.id===leavingId);
       const si=s.spectators.findIndex(p=>p.id===leavingId);
       const name=idx>=0?(s.players[idx].name||leavingName):(si>=0?s.spectators[si].name:leavingName);
       s.log=s.log||[];
       const chat=Array.isArray(s.chat)?s.chat:Object.values(s.chat||{});

       if(idx<0&&si>=0){
         s.spectators.splice(si,1);
         s.log.push(`👀 ${name} הפסיק לצפות במשחק.`);
         chat.push({id:crypto.randomUUID(),playerId:'system',playerIndex:-1,name:'מערכת',text:`${name} הפסיק לצפות במשחק`,ts:Date.now(),system:true});
         s.chat=chat.slice(-60);
         return s
       }

       if(idx>=0){
         // Never delete a player seat. This is what makes later re-entry possible.
         s.players[idx].left=true;
         s.log.push(`🚪 ${name} יצא מהמשחק.`);
         chat.push({id:crypto.randomUUID(),playerId:'system',playerIndex:-1,name:'מערכת',text:`${name} יצא מהמשחק - הוא יכול לחזור בכל רגע`,ts:Date.now(),system:true});
         s.chat=chat.slice(-60);

         if(s.host===leavingId){
           const nh=s.players.find((p,i)=>i!==idx&&!p.left);
           if(nh)s.host=nh.id;
         }

         if(s.phase!=='lobby'){
           if(s.pendingDiscards?.[idx]!==undefined){
             delete s.pendingDiscards[idx];
             if(Object.keys(s.pendingDiscards).length===0&&s.turnPhase==='discard'){
               s.turnPhase='moveRobber';
               s.robberResume='postroll'
             }
           }

           if(s.currentPlayer===idx){
             const next=nextActivePlayer(s,idx);
             if(next!==null){
               s.tradeOffer=null;
               delete s.freeRoads;
               delete s.pendingDiscards;
               delete s.robberResume;
               delete s.robberVictims;
               s.currentPlayer=next;
               s.turnPhase='preroll';
               s.dice=null;
               s.turnCounter=(s.turnCounter||0)+1;
               s.players[next].devPlayed=false;
               s.log.push(`➡️ התור עבר אוטומטית ל-${s.players[next].name}.`)
             }
           }
         }
       }

       return s
     },{applyLocally:false})
   }catch(e){console.warn('Could not broadcast leave event',e)}
 }

 if(unsub)unsub();
 unsub=null;
 state=null;
 screen='home';
 code='';
 uiMode=null;
 lastAlertedTurnKey=null;
 lastSeenStealId=null;
 history.replaceState({},'',location.pathname);
 render()
}
function showStealToast(evt){
 const old=document.getElementById('stealToast');if(old)old.remove();
 const pi=myIndex();
 const div=document.createElement('div');
 div.id='stealToast';
 div.className='steal-toast';

 let title='🎒 גניבה!';
 let sub=`${evt.thiefName} גנב קלף משאב אקראי מ-${evt.victimName}`;
 if(evt.thiefId===myId){
   title='🎒 גנבת קלף!';
   sub=`גנבת קלף משאב אקראי מ-${evt.victimName}`;
 }else if(evt.victimId===myId){
   title='🚨 גנבו ממך!';
   sub=`${evt.thiefName} גנב ממך קלף משאב אקראי`;
 }
 div.innerHTML=`<b>${title}</b><span>${sub}</span>`;
 document.body.appendChild(div);
 requestAnimationFrame(()=>div.classList.add('show'));
 clearTimeout(stealToastTimer);
 stealToastTimer=setTimeout(()=>{div.classList.remove('show');setTimeout(()=>div.remove(),250)},5000);
 try{if(evt.victimId===myId&&'vibrate' in navigator)navigator.vibrate([250,100,250,100,350])}catch(e){}
}
function alertSteal(s){
 const evt=s?.lastSteal;
 if(!evt?.id||evt.id===lastSeenStealId)return;
 lastSeenStealId=evt.id;
 showStealToast(evt);
}

function showTurnToast(){
 const old=document.getElementById('turnToast');if(old)old.remove();
 const div=document.createElement('div');
 div.id='turnToast';
 div.className='turn-toast';
 div.innerHTML='🚨 <b>צבע אדום!</b><span>התור שלך - אפשר להטיל קוביות ולהמשיך במשחק</span>';
 document.body.appendChild(div);
 requestAnimationFrame(()=>div.classList.add('show'));
 clearTimeout(turnToastTimer);
 turnToastTimer=setTimeout(()=>{div.classList.remove('show');setTimeout(()=>div.remove(),250)},5000);
}
async function ensureNotificationPermission(){
 if(!('Notification' in window))return;
 if(Notification.permission==='default'){
   try{await Notification.requestPermission()}catch(e){}
 }
}
function alertMyTurn(s){
 if(!s||s.phase!=='playing')return;
 const players=Array.isArray(s.players)?s.players:Object.values(s.players||{});
 const pi=players.findIndex(p=>p.id===myId);
 if(pi<0||s.currentPlayer!==pi||s.turnPhase!=='preroll')return;
 const key=`${s.turnCounter||0}:${s.currentPlayer}`;
 if(lastAlertedTurnKey===key)return;
 lastAlertedTurnKey=key;
 showTurnToast();
 try{
   if('Notification' in window&&Notification.permission==='granted'&&document.hidden){
     new Notification('צבע אדום',{body:'התור שלך - אפשר להטיל קוביות.'});
   }
 }catch(e){}
 try{if('vibrate' in navigator)navigator.vibrate([180,80,180])}catch(e){}
}


let repairInProgress=false;
async function repairRoomIfNeeded(){
 if(repairInProgress||!state||state.phase!=='playing')return;

 let needs=false;

 if(state.turnPhase==='discard' && state.pendingDiscards){
   needs=Object.keys(state.pendingDiscards).some(k=>!isActivePlayer(state.players[Number(k)]));
 }
 if(!isActivePlayer(state.players[state.currentPlayer]))needs=true;

 if(!needs)return;

 repairInProgress=true;
 try{
   await runTransaction(roomRef(code),s=>{
     if(!s)return s;
     s.players=ps(s);
     normalizeSpectators(s);
     return repairBlockedState(s)
   },{applyLocally:false})
 }catch(e){
   console.warn('Automatic room repair failed',e)
 }finally{
   repairInProgress=false
 }
}

function subscribe(c){if(unsub)unsub();unsub=onValue(roomRef(c),snap=>{const s=snap.val();if(!s){err='החדר לא קיים';screen='home';state=null;render();return}state=s;state.players=ps(state);normalizeSpectators(state);screen=s.phase==='lobby'?'lobby':'game';render();alertMyTurn(state);alertSteal(state);repairRoomIfNeeded()})}
async function resume(){if(!code||!ready)return;const s=(await get(roomRef(code))).val();if(s&&(ps(s).some(p=>p.id===myId)||spectators(s).some(p=>p.id===myId)))subscribe(code);else render()}
window.vertexClick=placeVertex;window.edgeClick=placeEdge;window.moveRobberClick=moveRobber;window.victimClick=chooseVictim;window.playDevClick=playDev;
try{const app=initializeApp(firebaseConfig);db=getDatabase(app);ready=true;render();await resume()}catch(e){ferr=e.message;render()}
