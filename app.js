/* Hexland — a central place theory game
   app.js: game model (threshold/range/allocation), canvas renderer, optional ArcGIS Online view,
   scoring, result card, and UI wiring. Configuration constants are at the top of the file.
   Loaded at the end of index.html so the DOM is ready. */

(function(){
"use strict";

// ---------- Configuration ----------
// Optional: paste an ArcGIS Location Platform / ArcGIS Online API key here to use Esri basemaps
// (topographic, imagery, etc.). With no key the map uses the OpenStreetMap basemap, which needs none.
const ARCGIS_API_KEY="";
const ARCGIS_BASEMAP_WITH_KEY="arcgis/topographic";
// Optional: an ArcGIS Online web map item ID (from its URL: .../home/item.html?id=XXXX). If set, that web map
// is used as the basemap and layers, so you can build the background in your own AGO account. Needs to be shared publicly.
const ARCGIS_WEBMAP_ID="";
// Basemaps tried in order when there is no key and no web map. "topo", "satellite", "streets" etc. are Esri's
// ArcGIS Online basemaps that work without a key; "osm" is the OpenStreetMap fallback.
const ARCGIS_BASEMAPS=["topo","osm"];
const ARCGIS_TOGGLE_BASEMAP="satellite";
const ARCGIS_SDK_VERSION="4.32";
// Where the hex plain sits on the real map and how big a hex is (grid is 15 x 11 hexes ≈ 65 km x 41 km at 2.5 km).
const HEX_RADIUS_KM=2.5;
// Isotropic plain: High Plains near Garden City, Kansas — about as flat and featureless as land gets.
const MAP_CENTER_ISO={lon:-100.87,lat:37.97};
// River valley: the grid is centred on a real valley and the population pattern is generated from the river's
// course (dense near the river, sparse toward the hills), so the dense hexes line up with the real valley.
// "river" is a list of [lon,lat] points along the river; "hills" are centres of high ground with a radius in km.
const REAL_MAP_PRESETS={
  rio_grande:{
    name:'Rio Grande valley south of Albuquerque, New Mexico',
    center:{lon:-106.78,lat:34.55},
    river:[[-106.69,34.95],[-106.73,34.81],[-106.75,34.73],[-106.77,34.66],[-106.79,34.59],[-106.81,34.52],[-106.83,34.44],[-106.85,34.36],[-106.87,34.25]],
    hills:[{lon:-106.42,lat:34.62,r:16},{lon:-107.08,lat:34.42,r:12}]
  },
  missouri_kc:{
    name:'Missouri River, Leavenworth to Kansas City',
    center:{lon:-94.70,lat:39.24},
    river:[[-95.115,39.565],[-95.05,39.45],[-94.92,39.35],[-94.90,39.31],[-94.83,39.22],[-94.68,39.19],[-94.62,39.14],[-94.60,39.11],[-94.50,39.12],[-94.42,39.15],[-94.33,39.20],[-94.25,39.24]],
    hills:[]
  }
};
const REAL_MAP_PRESET='rio_grande';   // change to 'missouri_kc' (or add your own preset above) to move the valley

// ---------- Game definition ----------
const COLS=15, ROWS=11, BUDGET=180000, COVER_GOAL=0.95;
const GOODS=[
  {id:'bakery',  name:'Bakery',        order:'Low-order',  range:1, threshold:400,  cost:1000,  cssVar:'--bakery',  key:'1'},
  {id:'grocery', name:'Grocery store', order:'Middle-order',range:2, threshold:1000, cost:4000,  cssVar:'--grocery', key:'2'},
  {id:'hospital',name:'Hospital',      order:'High-order', range:4, threshold:2800, cost:15000, cssVar:'--hospital',key:'3'}
];
const GI=Object.fromEntries(GOODS.map((g,i)=>[g.id,i]));

// ---------- State ----------
let hexes=[], byKey=new Map(), pop=[], totalPop=0;
let state=null; // {name, mode, cash, fac:{bakery:Set,grocery:Set,hospital:Set}, tool, nextId}
let sim=null;   // computed allocation
let cssColor={}, size=30, originX=0, originY=0, dpr=1;
let arc=null; // ArcGIS state when the basemap view is active
let mapCenter=MAP_CENTER_ISO; // set per scenario in startGame
let chosenView='canvas';

// ---------- Hex geometry (pointy-top, odd-r offset) ----------
function axial(c,r){return [c-((r-(r&1))>>1), r];}
function cube(c,r){const [q,rr]=axial(c,r);return [q,-q-rr,rr];}
function hexDist(a,b){const A=cube(a.c,a.r),B=cube(b.c,b.r);return Math.max(Math.abs(A[0]-B[0]),Math.abs(A[1]-B[1]),Math.abs(A[2]-B[2]));}
const DIRS=[[1,0],[0,1],[-1,1],[-1,0],[0,-1],[1,-1]]; // E,SE,SW,W,NW,NE

function buildGrid(mode){
  hexes=[];byKey.clear();pop=[];totalPop=0;
  for(let r=0;r<ROWS;r++)for(let c=0;c<COLS;c++){
    const [q,rr]=axial(c,r);
    const h={i:hexes.length,c,r,q,rr,key:q+','+rr};
    hexes.push(h);byKey.set(h.key,h);
  }
  for(const h of hexes){
    h.nb=DIRS.map(([dq,dr])=>byKey.get((h.q+dq)+','+(h.rr+dr))||null);
    let p=100;
    if(mode==='real'){
      // Dense valley floor along the real river, thinning toward the hills
      const preset=REAL_MAP_PRESETS[REAL_MAP_PRESET];
      const [hx,hy]=hexKm(h);
      const riverKm=preset.river.map(([lon,lat])=>lonLatToKm(lon,lat));
      let d=Infinity;
      for(let i=0;i<riverKm.length-1;i++)d=Math.min(d,segDist(hx,hy,riverKm[i],riverKm[i+1]));
      const valley=Math.exp(-((d/6)**2));
      let hills=0;
      for(const hill of preset.hills){const [kx,ky]=lonLatToKm(hill.lon,hill.lat);hills+=Math.exp(-(((hx-kx)**2+(hy-ky)**2))/(hill.r*hill.r));}
      // floor of 80 keeps a well-placed bakery (7 hexes) just above its 400 threshold even in the hills
      p=Math.round((75+150*valley-20*hills)/5)*5;
      p=Math.max(80,Math.min(230,p));
    }
    pop[h.i]=p;totalPop+=p;
  }
}

// ---------- Simulation ----------
function simulate(){
  const res={goods:{},hier:{}};
  for(const g of GOODS){
    const facs=[...state.fac[g.id].values()];
    const serve=new Array(hexes.length).fill(null); // primary facility id (lowest id among nearest ties) or null
    const cust={};for(const f of facs)cust[f.id]=0;
    let servedPop=0;
    for(const h of hexes){
      let best=Infinity,ties=[];
      for(const f of facs){
        const d=hexDist(h,f);
        if(d>g.range)continue;
        if(d<best){best=d;ties=[f];}else if(d===best)ties.push(f);
      }
      if(ties.length){
        servedPop+=pop[h.i];
        for(const f of ties)cust[f.id]+=pop[h.i]/ties.length;
        serve[h.i]=ties.reduce((a,b)=>a.id<b.id?a:b).id;
      }
    }
    const failing=facs.filter(f=>cust[f.id]<g.threshold);
    res.goods[g.id]={facs,serve,cust,coverage:servedPop/totalPop,failing};
  }
  // hierarchy: higher-order facility located where all lower-order ones also exist
  function at(gid,c,r){for(const f of state.fac[gid].values())if(f.c===c&&f.r===r)return true;return false;}
  let hTotal=0,hOk=0;
  for(const f of state.fac.grocery.values()){hTotal++;if(at('bakery',f.c,f.r))hOk++;}
  for(const f of state.fac.hospital.values()){hTotal++;if(at('bakery',f.c,f.r)&&at('grocery',f.c,f.r))hOk++;}
  res.hier={total:hTotal,ok:hOk,pct:hTotal?hOk/hTotal:0};
  sim=res;
}

function facilityAt(gid,h){for(const f of state.fac[gid].values())if(f.c===h.c&&f.r===h.r)return f;return null;}

// ---------- Rendering ----------
const canvas=document.getElementById('map'), ctx=canvas.getContext('2d');
function readColors(){
  const cs=getComputedStyle(document.documentElement);
  for(const k of ['--bg','--panel','--ink','--muted','--line','--hex0','--hex1','--hexline','--bakery','--grocery','--hospital','--danger'])cssColor[k]=cs.getPropertyValue(k).trim();
}
function layout(){
  const wrap=canvas.parentElement;
  const cssW=Math.max(280,wrap.clientWidth-12);
  const pad=8;
  size=(cssW-2*pad)/(Math.sqrt(3)*(COLS+0.5));
  const cssH=size*(1.5*(ROWS-1)+2)+2*pad;
  dpr=Math.min(2,window.devicePixelRatio||1);
  canvas.style.height=cssH+'px';
  canvas.width=Math.round(cssW*dpr);canvas.height=Math.round(cssH*dpr);
  originX=pad+size*Math.sqrt(3)/2;originY=pad+size;
  for(const h of hexes){h.x=originX+size*Math.sqrt(3)*(h.c+0.5*(h.r&1));h.y=originY+size*1.5*h.r;}
  draw();
}
function corner(h,k,s){const a=Math.PI/180*(60*k-30);return [h.x+s*Math.cos(a),h.y+s*Math.sin(a)];}
function hexPath(h,s){ctx.beginPath();for(let k=0;k<6;k++){const [x,y]=corner(h,k,s);k?ctx.lineTo(x,y):ctx.moveTo(x,y);}ctx.closePath();}
function mix(a,b,t){ // hex colors
  const pa=parseInt(a.slice(1),16),pb=parseInt(b.slice(1),16);
  const r=Math.round(((pa>>16)&255)*(1-t)+((pb>>16)&255)*t),g=Math.round(((pa>>8)&255)*(1-t)+((pb>>8)&255)*t),bl=Math.round((pa&255)*(1-t)+(pb&255)*t);
  return `rgb(${r},${g},${bl})`;
}
function rgba(hex,a){const p=parseInt(hex.slice(1),16);return `rgba(${(p>>16)&255},${(p>>8)&255},${p&255},${a})`;}

function draw(){
  if(!state)return;
  ctx.setTransform(dpr,0,0,dpr,0,0);
  ctx.clearRect(0,0,canvas.width,canvas.height);
  const sel=GOODS[GI[state.tool]]||null;
  const selRes=sel?sim.goods[sel.id]:null;
  const selColor=sel?cssColor[sel.cssVar]:null;
  const maxPop=state.mode==='real'?230:100, minPop=state.mode==='real'?80:100;
  // base hexes
  for(const h of hexes){
    const t=maxPop===minPop?0.35:(pop[h.i]-minPop)/(maxPop-minPop);
    ctx.fillStyle=mix(cssColor['--hex0'],cssColor['--hex1'],t*0.9);
    hexPath(h,size);ctx.fill();
    if(selRes&&selRes.serve[h.i]!==null){
      const fid=selRes.serve[h.i];
      const shade=[0.22,0.34,0.46][fid%3];
      ctx.fillStyle=rgba(selColor,shade);ctx.fill();
    }
    ctx.strokeStyle=cssColor['--hexline'];ctx.lineWidth=1;ctx.stroke();
  }
  // market-area boundaries for selected good
  if(selRes){
    ctx.strokeStyle=selColor;ctx.lineWidth=Math.max(2,size*0.11);ctx.lineCap='round';
    for(const h of hexes){
      const a=selRes.serve[h.i];if(a===null)continue;
      for(let k=0;k<6;k++){
        const n=h.nb[k];
        const b=n?selRes.serve[n.i]:null;
        if(b===a)continue;
        if(n&&b!==null&&n.i<h.i)continue; // draw shared edge once
        const [x1,y1]=corner(h,k,size),[x2,y2]=corner(h,(k+1)%6,size);
        ctx.beginPath();ctx.moveTo(x1,y1);ctx.lineTo(x2,y2);ctx.stroke();
      }
    }
  }
  // facilities, largest (highest order) first so stacked ones stay visible
  for(const g of [...GOODS].reverse()){
    const r=sim.goods[g.id];const isSel=sel&&sel.id===g.id;
    for(const f of r.facs){
      const h=hexes[f.hex];
      const failing=r.cust[f.id]<g.threshold;
      const base=[0.22,0.3,0.38][GI[g.id]]*size;
      const rad=isSel?base*1.15:base;
      ctx.beginPath();
      if(g.id==='bakery'){ctx.arc(h.x,h.y,rad,0,Math.PI*2);}
      else if(g.id==='grocery'){ctx.rect(h.x-rad,h.y-rad,rad*2,rad*2);}
      else {for(let k=0;k<6;k++){const a=Math.PI/180*(60*k);const x=h.x+rad*1.1*Math.cos(a),y=h.y+rad*1.1*Math.sin(a);k?ctx.lineTo(x,y):ctx.moveTo(x,y);}ctx.closePath();}
      ctx.fillStyle=cssColor[g.cssVar];ctx.fill();
      ctx.strokeStyle=cssColor['--panel'];ctx.lineWidth=Math.max(1.5,size*0.06);ctx.stroke();
      if(g.id==='hospital'){ctx.strokeStyle=cssColor['--panel'];ctx.lineWidth=Math.max(2,rad*0.32);ctx.beginPath();ctx.moveTo(h.x-rad*0.55,h.y);ctx.lineTo(h.x+rad*0.55,h.y);ctx.moveTo(h.x,h.y-rad*0.55);ctx.lineTo(h.x,h.y+rad*0.55);ctx.stroke();}
      if(failing){
        ctx.setLineDash([size*0.12,size*0.1]);ctx.strokeStyle=cssColor['--danger'];ctx.lineWidth=Math.max(2,size*0.09);
        ctx.beginPath();ctx.arc(h.x,h.y,rad*1.55+2,0,Math.PI*2);ctx.stroke();ctx.setLineDash([]);
        ctx.fillStyle=cssColor['--danger'];ctx.font=`700 ${Math.max(10,size*0.5)}px "Bricolage Grotesque",sans-serif`;ctx.textAlign='center';ctx.textBaseline='middle';
        ctx.fillText('!',h.x+rad*1.7,h.y-rad*1.5);
      }
    }
  }
  if(arc&&arc.ready){try{drawArc();}catch(e){arcLog('drawArc FAILED: '+errText(e));}}
}

// ---------- Geography helpers (km offsets from the scenario's map centre; north is +y) ----------
function kmToLon(km,lat){return km/(111.32*Math.cos(lat*Math.PI/180));}
function kmToLat(km){return km/110.574;}
function lonLatToKm(lon,lat){return [(lon-mapCenter.lon)*111.32*Math.cos(mapCenter.lat*Math.PI/180),(lat-mapCenter.lat)*110.574];}
function hexKm(h){
  const cx=(COLS-1)/2+0.25, cy=(ROWS-1)/2;
  return [(h.c+0.5*(h.r&1)-cx)*Math.sqrt(3)*HEX_RADIUS_KM, -(h.r-cy)*1.5*HEX_RADIUS_KM];
}
function segDist(px,py,a,b){
  const vx=b[0]-a[0],vy=b[1]-a[1];const L=vx*vx+vy*vy;
  const t=L?Math.max(0,Math.min(1,((px-a[0])*vx+(py-a[1])*vy)/L)):0;
  return Math.hypot(px-(a[0]+t*vx),py-(a[1]+t*vy));
}
// ---------- ArcGIS Online view (optional) ----------
function hexLonLat(h){
  const [dx,dy]=hexKm(h);
  return [mapCenter.lon+kmToLon(dx,mapCenter.lat), mapCenter.lat+kmToLat(dy)];
}
function hexCornerLonLat(h,k){
  const [lon,lat]=hexLonLat(h);
  const a=Math.PI/180*(60*k-30);
  return [lon+kmToLon(HEX_RADIUS_KM*Math.cos(a),mapCenter.lat), lat-kmToLat(HEX_RADIUS_KM*Math.sin(a))];
}
function clockwise(ring){let a=0;for(let i=0;i<ring.length-1;i++)a+=(ring[i+1][0]-ring[i][0])*(ring[i+1][1]+ring[i][1]);return a>0;}
function hexRing(h){const ring=[0,1,2,3,4,5,0].map(k=>hexCornerLonLat(h,k));return clockwise(ring)?ring:ring.reverse();}
function hexToRgb(hex){const p=parseInt(hex.slice(1),16);return [(p>>16)&255,(p>>8)&255,p&255];}
function lonLatToHex(lon,lat){
  // km offsets from the grid centre, then nearest hex centre (within one hex radius)
  const [dx,dy]=lonLatToKm(lon,lat);
  let best=null,bd=Infinity;
  for(const h of hexes){
    const [hx,hy]=hexKm(h);
    const d=(hx-dx)**2+(hy-dy)**2;if(d<bd){bd=d;best=h;}
  }
  return (best&&bd<=HEX_RADIUS_KM*HEX_RADIUS_KM)?best:null;
}
function hexFromMapPoint(mp){
  if(!mp)return null;
  let lon=mp.longitude,lat=mp.latitude;
  if((lon===undefined||lat===undefined)&&mp.x!==undefined){ // Web Mercator metres → lon/lat
    lon=mp.x/6378137*180/Math.PI;lat=(2*Math.atan(Math.exp(mp.y/6378137))-Math.PI/2)*180/Math.PI;
  }
  if(lon===undefined||lat===undefined||isNaN(lon)||isNaN(lat))return null;
  return lonLatToHex(lon,lat);
}
function arcLog(msg){
  const box=$('arcLogBox'),pre=$('arcLog');if(!box||!pre)return;
  box.style.display='block';
  const t=new Date().toISOString().slice(11,19);
  pre.textContent+=`[${t}] ${msg}\n`;pre.scrollTop=pre.scrollHeight;
  try{console.log('[Hexland map]',msg);}catch(e){}
}
function errText(e){if(!e)return 'unknown error';if(typeof e==='string')return e;return (e.name?e.name+': ':'')+(e.message||e.details&&JSON.stringify(e.details)||String(e));}
window.addEventListener('unhandledrejection',ev=>{if(arc||chosenView==='arc')arcLog('Unhandled promise rejection: '+errText(ev.reason));});
(function(){const orig=console.error;console.error=function(){try{if(arc||chosenView==='arc')arcLog('console.error: '+Array.from(arguments).map(a=>typeof a==='string'?a:errText(a)).join(' '));}catch(e){}return orig.apply(console,arguments);};})();
function arcStatus(msg,isError){const el=$('arcStatus');el.textContent=msg||'';el.style.display=msg?'block':'none';el.style.color=isError?'var(--danger)':'var(--muted)';}

function loadArcSDK(){
  return new Promise((resolve,reject)=>{
    if(window.require&&window.require.toUrl){arcLog('SDK already loaded');resolve();return;}
    arcLog(`Page URL: ${location.href}`);
    arcLog(`Loading SDK ${ARCGIS_SDK_VERSION} from js.arcgis.com…`);
    const css=document.createElement('link');css.rel='stylesheet';css.href=`https://js.arcgis.com/${ARCGIS_SDK_VERSION}/esri/themes/light/main.css`;
    css.onload=()=>arcLog('SDK stylesheet loaded');css.onerror=()=>arcLog('SDK stylesheet FAILED to load');
    document.head.appendChild(css);
    const sc=document.createElement('script');sc.src=`https://js.arcgis.com/${ARCGIS_SDK_VERSION}/`;
    sc.onload=()=>{arcLog('SDK script loaded; require is '+typeof window.require);resolve();};
    sc.onerror=()=>reject(new Error(`Could not download the ArcGIS SDK from js.arcgis.com/${ARCGIS_SDK_VERSION}. Check the internet connection or a content blocker.`));
    document.head.appendChild(sc);
  });
}
async function startArc(){
  arcStatus('Loading the ArcGIS Maps SDK…');
  await loadArcSDK();
  arcStatus('Building the map…');
  arcLog('Requesting modules…');
  return new Promise((resolve,reject)=>{
    const timer=setTimeout(()=>reject(new Error('The map took too long to become ready (30 s). The basemap tiles may be blocked.')),30000);
    window.require(["esri/config","esri/Map","esri/WebMap","esri/Basemap","esri/views/MapView","esri/layers/GraphicsLayer","esri/Graphic",
                    "esri/geometry/Polygon","esri/geometry/Polyline","esri/geometry/Point",
                    "esri/symbols/SimpleFillSymbol","esri/symbols/SimpleLineSymbol","esri/symbols/SimpleMarkerSymbol","esri/symbols/TextSymbol","esri/widgets/BasemapToggle"],
      (esriConfig,Map,WebMap,Basemap,MapView,GraphicsLayer,Graphic,Polygon,Polyline,Point,SimpleFillSymbol,SimpleLineSymbol,SimpleMarkerSymbol,TextSymbol,BasemapToggle)=>{
        try{
          arcLog('Modules resolved. SDK version reported: '+(esriConfig.version||'?'));
          const cont=document.getElementById('arcmap');arcLog(`Container size ${cont.clientWidth}×${cont.clientHeight}px, display ${getComputedStyle(cont).display}`);
          const wgs={wkid:4326};
          const hexLayer=new GraphicsLayer({title:'hexes'}),lineLayer=new GraphicsLayer({title:'market areas'}),facLayer=new GraphicsLayer({title:'facilities'});
          let map,basemapQueue=[];
          if(ARCGIS_API_KEY){esriConfig.apiKey=ARCGIS_API_KEY;}
          if(ARCGIS_WEBMAP_ID){
            arcLog('Using ArcGIS Online web map '+ARCGIS_WEBMAP_ID);
            map=new WebMap({portalItem:{id:ARCGIS_WEBMAP_ID}});
            map.addMany([hexLayer,lineLayer,facLayer]);
          }else{
            basemapQueue=ARCGIS_API_KEY?[ARCGIS_BASEMAP_WITH_KEY,...ARCGIS_BASEMAPS]:[...ARCGIS_BASEMAPS];
            arcLog((ARCGIS_API_KEY?'Using API key. ':'No API key. ')+'Basemaps to try: '+basemapQueue.join(', '));
            map=new Map({basemap:basemapQueue.shift(),layers:[hexLayer,lineLayer,facLayer]});
          }
          const view=new MapView({container:"arcmap",map,center:[mapCenter.lon,mapCenter.lat],zoom:10,constraints:{rotationEnabled:false},popupEnabled:false});
          arcLog('Map centre '+mapCenter.lon+', '+mapCenter.lat+(state.mode==='real'?' ('+REAL_MAP_PRESETS[REAL_MAP_PRESET].name+')':' (High Plains, Kansas)'));
          const hexGraphics=hexes.map(h=>new Graphic({
            geometry:new Polygon({rings:[hexRing(h)],spatialReference:wgs}),
            attributes:{hex:h.i},
            symbol:new SimpleFillSymbol({color:[109,182,63,0.3],outline:{color:[42,26,10,0.85],width:1.2}})
          }));
          hexLayer.addMany(hexGraphics);
          arcLog(`Created ${hexGraphics.length} hex graphics; first ring starts at ${JSON.stringify(hexRing(hexes[0])[0].map(v=>+v.toFixed(4)))}`);
          try{
            let logged=false;
            view.watch('updating',v=>{if(!v&&!logged){logged=true;arcLog('View finished its first update (tiles and graphics drawn)');
              try{
                const cssApplied=getComputedStyle(cont).position==='relative';
                arcLog('SDK stylesheet applied to container: '+(cssApplied?'yes':'NO'));
                const cv=cont.querySelector('canvas');
                if(cv){const r=cv.getBoundingClientRect();const cs=getComputedStyle(cv);arcLog(`Map canvas: attribute size ${cv.width}×${cv.height}, on-screen ${Math.round(r.width)}×${Math.round(r.height)}px at (${Math.round(r.left)},${Math.round(r.top)}), display ${cs.display}, visibility ${cs.visibility}, opacity ${cs.opacity}`);}
                else arcLog('No canvas element found inside the map container');
                const root=cont.querySelector('.esri-view-root');if(root){const rr=root.getBoundingClientRect();arcLog(`esri-view-root on-screen ${Math.round(rr.width)}×${Math.round(rr.height)}px`);}
                const el=cont;let covered=null;const r2=el.getBoundingClientRect();const topEl=document.elementFromPoint(r2.left+r2.width/2,r2.top+r2.height/2);
                if(topEl&&!el.contains(topEl))covered=topEl.tagName+(topEl.id?'#'+topEl.id:'')+(topEl.className&&typeof topEl.className==='string'?'.'+topEl.className.split(' ').join('.'):'');
                arcLog('Element at map centre: '+(covered?('COVERED by '+covered):'the map itself'));
              }catch(e){arcLog('Geometry check failed: '+errText(e));}
            }});
            try{const t=document.createElement('canvas');arcLog('WebGL available: '+(!!(t.getContext('webgl2')||t.getContext('webgl'))));}catch(e){}
            const tryBasemap=()=>{
              const bm=map.basemap;if(!bm){arcLog('No basemap object on the map');return;}
              bm.load().then(()=>{
                // a basemap can "load" yet have a base layer that failed; check the first base layer too
                const bl=bm.baseLayers&&bm.baseLayers.getItemAt(0);
                const p=bl&&bl.load?bl.load():Promise.resolve();
                return p.then(()=>arcLog('Basemap loaded: '+(bm.title||bm.id||'ok')+(bl?(' ('+(bl.title||bl.url||bl.type)+')'):'')));
              }).catch(e=>{
                arcLog('Basemap "'+(bm.title||bm.id||'?')+'" FAILED: '+errText(e));
                if(basemapQueue.length){const next=basemapQueue.shift();arcLog('Trying basemap '+next);map.basemap=next;tryBasemap();}
              });
            };
            tryBasemap();
          }catch(e){arcLog('Instrumentation skipped: '+errText(e));}
          arc={ready:false,view,Graphic,Polyline,Point,SimpleFillSymbol,SimpleLineSymbol,SimpleMarkerSymbol,TextSymbol,wgs,hexLayer,lineLayer,facLayer,hexGraphics};
          view.when(()=>{
            clearTimeout(timer);
            arc.ready=true;
            arcStatus('');
            arcLog(`View ready. Spatial reference wkid ${view.spatialReference&&view.spatialReference.wkid}, zoom ${view.zoom}, centre ${view.center&&[+view.center.longitude.toFixed(3),+view.center.latitude.toFixed(3)]}`);
            view.goTo(hexGraphics,{animate:false}).then(()=>arcLog('Zoomed to hex grid, zoom '+(+view.zoom.toFixed(2)))).catch(e=>arcLog('goTo failed: '+errText(e)));
            try{drawArc();arcLog(`Drew ${hexLayer.graphics.length} hexes, ${lineLayer.graphics.length} boundary lines, ${facLayer.graphics.length} facility markers`);}catch(e){arcLog('drawArc FAILED: '+errText(e));}
            if(!ARCGIS_WEBMAP_ID&&ARCGIS_TOGGLE_BASEMAP){
              try{view.ui.add(new BasemapToggle({view,nextBasemap:ARCGIS_TOGGLE_BASEMAP}),"bottom-right");}catch(e){arcLog('Basemap toggle skipped: '+errText(e));}
            }
            view.on("click",ev=>{
              // Primary: geometry lookup from the clicked map coordinate. Fallback: the SDK's hitTest.
              const h=hexFromMapPoint(ev.mapPoint);
              if(h){arcLog('Click on hex '+h.i+' with tool '+state.tool);place(h);return;}
              view.hitTest(ev,{include:hexLayer}).then(r=>{
                const hit=(r.results||[]).find(x=>x.graphic&&x.graphic.attributes&&x.graphic.attributes.hex!==undefined);
                if(hit){arcLog('Click (hitTest) on hex '+hit.graphic.attributes.hex+' with tool '+state.tool);place(hexes[hit.graphic.attributes.hex]);}
                else arcLog('Click outside the grid');
              }).catch(e=>arcLog('hitTest failed: '+errText(e)));
            });
            view.on("pointer-move",ev=>{
              try{const mp=view.toMap({x:ev.x,y:ev.y});showHover(hexFromMapPoint(mp));}catch(e){}
            });
            view.on("pointer-leave",()=>showHover(null));
            resolve();
          }).catch(err=>{clearTimeout(timer);arcLog('view.when rejected: '+errText(err));reject(err||new Error('The view failed to initialise.'));});
        }catch(e){clearTimeout(timer);arcLog('Setup threw: '+errText(e));reject(e);}
      },err=>{clearTimeout(timer);arcLog('Module load failed: '+errText(err));reject(err);});
  });
}
function stopArc(){
  if(arc&&arc.view){try{arc.view.destroy();}catch(e){}}
  arc=null;arcStatus('');
}
function drawArc(){
  const {Graphic,Polyline,Point,SimpleFillSymbol,SimpleLineSymbol,SimpleMarkerSymbol,TextSymbol,wgs,hexGraphics,lineLayer,facLayer}=arc;
  const sel=GOODS[GI[state.tool]]||null;
  const selRes=sel?sim.goods[sel.id]:null;
  const selRgb=sel?hexToRgb(cssColor[sel.cssVar]):null;
  const maxPop=state.mode==='real'?230:100,minPop=state.mode==='real'?80:100;
  for(const h of hexes){
    const t=maxPop===minPop?0.3:0.15+0.5*(pop[h.i]-minPop)/(maxPop-minPop);
    let color=[109,182,63,t];
    if(selRes&&selRes.serve[h.i]!==null){const a=[0.4,0.52,0.64][selRes.serve[h.i]%3];color=[selRgb[0],selRgb[1],selRgb[2],a];}
    hexGraphics[h.i].symbol=new SimpleFillSymbol({color,outline:{color:[42,26,10,0.85],width:1.2}});
  }
  lineLayer.removeAll();
  if(selRes){
    const lines=[];
    const lineSym=new SimpleLineSymbol({color:[selRgb[0],selRgb[1],selRgb[2],1],width:3,cap:"round"});
    for(const h of hexes){
      const a=selRes.serve[h.i];if(a===null)continue;
      for(let k=0;k<6;k++){
        const n=h.nb[k];const b=n?selRes.serve[n.i]:null;
        if(b===a)continue;if(n&&b!==null&&n.i<h.i)continue;
        lines.push(new Graphic({geometry:new Polyline({paths:[[hexCornerLonLat(h,k),hexCornerLonLat(h,(k+1)%6)]],spatialReference:wgs}),symbol:lineSym}));
      }
    }
    lineLayer.addMany(lines);
  }
  facLayer.removeAll();
  const marks=[];
  const styles={bakery:"circle",grocery:"square",hospital:"diamond"};
  for(const g of [...GOODS].reverse()){
    const r=sim.goods[g.id];const isSel=sel&&sel.id===g.id;
    const rgb=hexToRgb(cssColor[g.cssVar]);
    const base=[9,12,16][GI[g.id]]*(isSel?1.2:1);
    for(const f of r.facs){
      const [lon,lat]=hexLonLat(hexes[f.hex]);
      const pt=new Point({longitude:lon,latitude:lat,spatialReference:wgs});
      const failing=r.cust[f.id]<g.threshold;
      if(failing){
        marks.push(new Graphic({geometry:pt,symbol:new SimpleMarkerSymbol({style:"circle",size:base*2.2,color:[0,0,0,0],outline:{color:[198,40,40,1],width:2}})}));
        marks.push(new Graphic({geometry:pt,symbol:new TextSymbol({text:"!",color:[198,40,40,1],xoffset:base*1.3,yoffset:base*0.9,font:{size:14,weight:"bold"}})}));
      }
      marks.push(new Graphic({geometry:pt,symbol:new SimpleMarkerSymbol({style:styles[g.id],size:base,color:[rgb[0],rgb[1],rgb[2],1],outline:{color:[255,255,255,1],width:1.5}})}));
      if(g.id==='hospital')marks.push(new Graphic({geometry:pt,symbol:new SimpleMarkerSymbol({style:"cross",size:base*0.6,color:[0,0,0,0],outline:{color:[255,255,255,1],width:2}})}));
    }
  }
  facLayer.addMany(marks);
}

// ---------- UI ----------
const $=id=>document.getElementById(id);
function money(n){return '$'+Math.round(n).toLocaleString('en-US');}
function pct(x){return Math.round(x*100)+'%';}

function buildTools(){
  const el=$('tools');el.innerHTML='';
  for(const g of GOODS){
    const b=document.createElement('button');b.className='tool';b.dataset.tool=g.id;b.setAttribute('aria-pressed','false');
    b.innerHTML=`<span class="sw" style="background:var(${g.cssVar})"></span><span><span class="name">${g.name}</span><br><span class="meta">${g.order}. Range ${g.range} hex${g.range>1?'es':''}, threshold ${g.threshold.toLocaleString('en-US')}</span></span><span class="cost">${money(g.cost)}</span>`;
    b.addEventListener('click',()=>setTool(g.id));el.appendChild(b);
  }
  const x=document.createElement('button');x.className='tool bull';x.dataset.tool='bulldoze';x.setAttribute('aria-pressed','false');
  x.innerHTML=`<span class="sw"></span><span><span class="name">Bulldoze</span><br><span class="meta">Remove a facility, get half the cost back</span></span><span class="cost"></span>`;
  x.addEventListener('click',()=>setTool('bulldoze'));el.appendChild(x);
}
function setTool(t){state.tool=t;document.querySelectorAll('.tool').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.tool===t)));draw();updateHint();}

function updatePanel(){
  $('cash').textContent=money(state.cash);
  $('cashbar').style.width=(100*state.cash/BUDGET)+'%';
  const cov=$('cov');cov.innerHTML='';
  for(const g of GOODS){
    const r=sim.goods[g.id];
    const row=document.createElement('div');row.className='row';
    const fails=r.failing.length;
    row.innerHTML=`<span class="lbl"><span class="sw" style="background:var(${g.cssVar})"></span>${g.name}</span><span>${pct(r.coverage)} served</span>
      <div class="bar"><i style="width:${Math.min(100,r.coverage*100)}%;background:var(${g.cssVar})"></i></div>
      <span class="sub">${r.facs.length} built${fails?` · <span class="bad">${fails} below threshold</span>`:''}</span>`;
    cov.appendChild(row);
  }
  const hrow=document.createElement('div');hrow.className='row';
  hrow.innerHTML=`<span class="lbl">Hierarchy</span><span>${sim.hier.total?pct(sim.hier.pct):'–'}</span><span class="sub">Higher-order facilities placed where all lower-order goods already exist: ${sim.hier.ok} of ${sim.hier.total}</span>`;
  cov.appendChild(hrow);
  const meta=state.mode==='real'?'River valley':'Isotropic plain';
  $('who').textContent=(state.name?state.name+' · ':'')+meta+' · '+totalPop.toLocaleString('en-US')+' people';
}

let lastHintKey='';
function updateHint(text,cls,key){
  const el=$('hint');
  if(text){el.textContent=text;el.className='hint'+(cls?' '+cls:'');return;}
  // contextual defaults
  const g=GOODS[GI[state.tool]];
  const built=GOODS.reduce((n,g)=>n+state.fac[g.id].size,0);
  let msg='',c='';
  const anyFail=GOODS.find(g=>sim.goods[g.id].failing.length);
  if(anyFail){const f=sim.goods[anyFail.id].failing[0];msg=`A ${anyFail.name.toLowerCase()} has only ${Math.round(sim.goods[anyFail.id].cust[f.id]).toLocaleString('en-US')} customers, under its threshold of ${anyFail.threshold.toLocaleString('en-US')}. Too many of the same good too close together split the customers. Bulldoze one or spread them out.`;c='warn';}
  else if(built===0)msg='Pick a facility on the right, then click a hex to build it. Try a hospital first and watch how far its market area reaches.';
  else if(state.tool==='bulldoze')msg='Click a facility to remove it. You get half its cost back.';
  else if(g&&g.id!=='bakery'&&sim.hier.total&&sim.hier.pct<0.5)msg='In Christaller\'s hierarchy a town with a hospital also has groceries and bakeries. Stacking higher-order goods on lower-order places raises your hierarchy score.';
  else if(g){const cov=sim.goods[g.id].coverage;msg=cov>=COVER_GOAL?`${g.name} coverage is ${pct(cov)}. Every extra one now costs money without helping.`:`${g.name}: ${pct(cov)} of people are within ${g.range} hex${g.range>1?'es':''} of one. Look for gaps in the shaded market areas.`;c=cov>=COVER_GOAL?'good':'';}
  el.textContent=msg;el.className='hint'+(c?' '+c:'');
}

function hexAtPointer(ev){
  const rect=canvas.getBoundingClientRect();
  const x=ev.clientX-rect.left,y=ev.clientY-rect.top;
  let best=null,bd=Infinity;
  for(const h of hexes){const d=(h.x-x)**2+(h.y-y)**2;if(d<bd){bd=d;best=h;}}
  return (best&&bd<=size*size)?best:null;
}

function place(h){
  if(!state||state.done)return;
  if(state.tool==='bulldoze'){
    // remove highest-order facility on this hex first
    for(const g of [...GOODS].reverse()){
      const f=facilityAt(g.id,h);
      if(f){state.fac[g.id].delete(f.id);state.cash+=g.cost/2;afterChange();updateHint(`Removed the ${g.name.toLowerCase()}. Refunded ${money(g.cost/2)}.`);return;}
    }
    updateHint('Nothing to bulldoze there.','warn');return;
  }
  const g=GOODS[GI[state.tool]];if(!g)return;
  if(facilityAt(g.id,h)){updateHint(`There is already a ${g.name.toLowerCase()} on that hex.`,'warn');return;}
  if(state.cash<g.cost){updateHint(`Not enough cash for a ${g.name.toLowerCase()} (${money(g.cost)}). Bulldoze something or open for inspection.`,'warn');return;}
  const f={id:state.nextId++,c:h.c,r:h.r,hex:h.i};
  state.fac[g.id].set(f.id,f);state.cash-=g.cost;
  afterChange();
  const cust=Math.round(sim.goods[g.id].cust[f.id]);
  if(cust<g.threshold)updateHint(`That ${g.name.toLowerCase()} draws only ${cust.toLocaleString('en-US')} customers, below its threshold of ${g.threshold.toLocaleString('en-US')}. It will fail unless the crowding is fixed.`,'warn');
  else updateHint();
}
function afterChange(){simulate();updatePanel();draw();}

canvas.addEventListener('click',ev=>{const h=hexAtPointer(ev);if(h)place(h);});
function showHover(h){
  const hv=$('hover');
  if(!h||!state){hv.style.display='none';return;}
  const parts=[`Population ${pop[h.i]}`];
  for(const g of GOODS){const r=sim.goods[g.id];const f=facilityAt(g.id,h);
    if(f)parts.push(`${g.name}: ${Math.round(r.cust[f.id]).toLocaleString('en-US')} customers`);
    else parts.push(`${g.name}: ${r.serve[h.i]!==null?'served':'no access'}`);}
  hv.innerHTML=parts.join('<br>');hv.style.display='block';
}
canvas.addEventListener('mousemove',ev=>showHover(hexAtPointer(ev)));
canvas.addEventListener('mouseleave',()=>showHover(null));
document.addEventListener('keydown',ev=>{
  if(!state||document.querySelector('.overlay.open'))return;
  const k=ev.key.toLowerCase();
  const g=GOODS.find(g=>g.key===k);if(g)setTool(g.id);else if(k==='x')setTool('bulldoze');
});

// ---------- Start / restart ----------
let chosenMode='iso';
$('modes').addEventListener('click',ev=>{const b=ev.target.closest('.mode');if(!b)return;chosenMode=b.dataset.mode;document.querySelectorAll('#modes .mode').forEach(m=>m.setAttribute('aria-pressed',String(m===b)));});
$('restartBtn').addEventListener('click',()=>{
  const built=state?GOODS.reduce((n,g)=>n+state.fac[g.id].size,0):0;
  if(built===0||confirm('Start a new game? Your current plan will be lost.'))location.reload();
});
$('learnBtn').addEventListener('click',()=>{$('learnOverlay').classList.add('open');});
document.querySelectorAll('[data-close]').forEach(b=>b.addEventListener('click',()=>$(b.dataset.close).classList.remove('open')));
document.addEventListener('keydown',ev=>{if(ev.key==='Escape')document.querySelectorAll('.overlay.open:not(#startOverlay)').forEach(o=>o.classList.remove('open'));});
$('views').addEventListener('click',ev=>{const b=ev.target.closest('.mode');if(!b)return;chosenView=b.dataset.view;document.querySelectorAll('#views .mode').forEach(m=>m.setAttribute('aria-pressed',String(m===b)));});
$('startBtn').addEventListener('click',async()=>{
  const name=$('nameIn').value.trim();
  stopArc();document.querySelector('.mapwrap').classList.remove('arc');
  startGame(name,chosenMode);
  $('startOverlay').classList.remove('open');
  if(chosenView==='arc'){
    document.querySelector('.mapwrap').classList.add('arc');
    try{
      await startArc();
    }catch(e){
      arcLog('Falling back to the abstract plain: '+errText(e));
      document.querySelector('.mapwrap').classList.remove('arc');stopArc();layout();
      const msg=(e&&(e.message||e.name))||String(e);
      arcStatus('ArcGIS map unavailable: '+msg+' Showing the abstract plain instead.',true);
    }
  }
});
window.addEventListener('error',ev=>{if(arc||chosenView==='arc'){const el=$('arcStatus');if(el&&!el.textContent)arcStatus('Script error: '+ev.message,true);}});
function startGame(name,mode){
  mapCenter=mode==='real'?REAL_MAP_PRESETS[REAL_MAP_PRESET].center:MAP_CENTER_ISO;
  readColors();buildGrid(mode);
  state={name,mode,cash:BUDGET,fac:{bakery:new Map(),grocery:new Map(),hospital:new Map()},tool:'hospital',nextId:1,done:false};
  buildTools();simulate();updatePanel();layout();setTool('hospital');updateHint();
}
window.addEventListener('resize',()=>{if(state)layout();});
const mq=window.matchMedia('(prefers-color-scheme: dark)');
(mq.addEventListener?mq.addEventListener('change',()=>{readColors();draw();}):mq.addListener(()=>{readColors();draw();}));

// ---------- Scoring, verdict, result card ----------
function scoreGame(){
  const covs=GOODS.map(g=>sim.goods[g.id].coverage);
  const failing=GOODS.reduce((n,g)=>n+sim.goods[g.id].failing.length,0);
  const allCovered=covs.every(c=>c>=COVER_GOAL);
  const win=allCovered&&failing===0;
  const avgCov=covs.reduce((a,b)=>a+b,0)/covs.length;
  const covPts=30*Math.min(1,avgCov/COVER_GOAL);
  const effPts=40*Math.max(0,Math.min(1,state.cash/(BUDGET*0.22)));
  const hierPts=30*sim.hier.pct;
  let score=Math.round(covPts+hierPts+effPts);
  if(!win)score=Math.min(score,Math.round(covPts+hierPts));
  const grade=score>=85?'A':score>=70?'B':score>=55?'C':score>=40?'D':'F';
  const reasons=[];
  for(const g of GOODS){const r=sim.goods[g.id];
    reasons.push(`${g.name}: ${pct(r.coverage)} of people served by ${r.facs.length} facilit${r.facs.length===1?'y':'ies'}${r.failing.length?`, ${r.failing.length} below threshold`:''}.`);}
  reasons.push(`Hierarchy: ${sim.hier.total?pct(sim.hier.pct):'no higher-order facilities'} of higher-order facilities sit on places that already have all lower-order goods.`);
  reasons.push(`Cash left: ${money(state.cash)} of ${money(BUDGET)}.`);
  return {win,score,grade,reasons,covs,failing,avgCov};
}
function hashCode(str){let h=2166136261;for(let i=0;i<str.length;i++){h^=str.charCodeAt(i);h=Math.imul(h,16777619)>>>0;}return h.toString(36).toUpperCase().padStart(7,'0').slice(-7);}
function verifyCode(name,date,mode,win,score){return hashCode(`${name.trim().toLowerCase()}|${date}|${mode}|${win?'W':'L'}|${score}`);}
function today(){const d=new Date();return d.getFullYear()+'-'+String(d.getMonth()+1).padStart(2,'0')+'-'+String(d.getDate()).padStart(2,'0');}

let lastResult=null;
$('submitBtn').addEventListener('click',async()=>{
  const res=scoreGame();const date=today();
  let snapshot=canvas;
  if(arc&&arc.ready){
    try{const shot=await arc.view.takeScreenshot({format:'png',width:1200});const img=new Image();img.src=shot.dataUrl;await img.decode();snapshot=img;}catch(e){snapshot=canvas;}
  }
  const code=verifyCode(state.name,date,state.mode,res.win,res.score);
  lastResult={...res,date,code};
  $('verdict').textContent=res.win?'You win':'Not yet';
  $('verdict').className='verdict '+(res.win?'win':'loss');
  const modeName=state.mode==='real'?'River valley':'Isotropic plain';
  $('resultBody').innerHTML=`<p><b>${state.name||'Planner'}</b> · ${modeName} · ${date} · Score <b>${res.score}/100</b>, grade <b>${res.grade}</b></p>
    <ul class="reasons">${res.reasons.map(r=>`<li>${r}</li>`).join('')}</ul>
    <p class="status">${res.win?'Everyone has access to every good and nothing is going broke. Score is 30 points for coverage, 30 for hierarchy, 40 for cash left.':'To win, reach 95% coverage for all three goods with no facility below threshold. Close this window to keep building; you can inspect as often as you like.'}</p>
    <p class="status">Verification code <code class="vc">${code}</code></p>`;
  drawCard(res,date,code,modeName,snapshot);
  $('summaryText').value=`Hexland result card\nName: ${state.name||'(no name)'}\nDate: ${date}\nLandscape: ${modeName}\nVerdict: ${res.win?'WIN':'LOSS (not yet)'}\nScore: ${res.score}/100 (${res.grade})\n${res.reasons.join('\n')}\nVerification code: ${code}`;
  $('saveStatus').textContent='Or take a screenshot of this card.';
  $('resultOverlay').classList.add('open');
});

function drawCard(res,date,code,modeName,snap){
  const cv=$('cardCanvas'),c=cv.getContext('2d');const W=cv.width,H=cv.height;
  c.setTransform(1,0,0,1,0,0);
  c.fillStyle='#FFFDF6';c.fillRect(0,0,W,H);
  c.fillStyle='#F3B62A';c.fillRect(0,0,W,10);
  const logo=$('logoImg');
  if(logo&&logo.complete&&logo.naturalWidth){const lh=96,lw=lh*logo.naturalWidth/logo.naturalHeight;c.drawImage(logo,36,24,lw,lh);}
  else{c.fillStyle='#2A1A0A';c.font='800 44px "Bricolage Grotesque",sans-serif';c.textBaseline='top';c.textAlign='left';c.fillText('Hexland',40,34);}
  c.textBaseline='top';c.textAlign='left';
  c.font='400 16px "Atkinson Hyperlegible",sans-serif';c.fillStyle='#6A5A3E';
  c.fillText('Central place theory result card',156,62);
  c.fillStyle=res.win?'#4E9A2E':'#C4384E';c.font='800 64px "Bricolage Grotesque",sans-serif';c.textAlign='right';
  c.fillText(res.win?'WIN':'LOSS',W-40,34);
  c.textAlign='left';c.fillStyle='#2A1A0A';
  c.font='700 22px "Atkinson Hyperlegible",sans-serif';c.fillText(state.name||'(no name entered)',40,130);
  c.font='400 18px "Atkinson Hyperlegible",sans-serif';c.fillStyle='#6A5A3E';
  c.fillText(`${date}   ${modeName}   ${totalPop.toLocaleString('en-US')} people`,40,160);
  c.fillStyle='#2A1A0A';c.font='800 40px "Bricolage Grotesque",sans-serif';c.fillText(`Score ${res.score}/100`,40,200);
  c.font='700 22px "Atkinson Hyperlegible",sans-serif';c.fillText(`Grade ${res.grade}`,40,250);
  // stats
  let y=300;c.font='400 17px "Atkinson Hyperlegible",sans-serif';
  const colors={bakery:'#E39A12',grocery:'#1E7FD0',hospital:'#C4384E'};
  for(const g of GOODS){const r=sim.goods[g.id];
    c.fillStyle=colors[g.id];c.beginPath();c.arc(48,y+9,7,0,Math.PI*2);c.fill();
    c.fillStyle='#2A1A0A';c.fillText(`${g.name}: ${pct(r.coverage)} served, ${r.facs.length} built${r.failing.length?`, ${r.failing.length} failing`:''}`,66,y);y+=30;}
  c.fillText(`Hierarchy: ${sim.hier.total?pct(sim.hier.pct):'–'}   Cash left: ${money(state.cash)}`,40,y);y+=30;
  c.fillStyle='#6A5A3E';c.fillText('Verification code',40,y+16);c.fillStyle='#2A1A0A';c.font='700 24px ui-monospace,Menlo,Consolas,monospace';c.fillText(code,190,y+12);
  // map snapshot
  const sw=snap.naturalWidth||snap.width,sh=snap.naturalHeight||snap.height;
  const mx=W/2+10,my=116,mw=W/2-50,mh=H-146;const scale=Math.min((mw-12)/sw,(mh-12)/sh);
  const dw=sw*scale,dh=sh*scale;
  c.fillStyle='#E4EFF9';c.fillRect(mx,my,mw,mh);
  c.drawImage(snap,mx+(mw-dw)/2,my+(mh-dh)/2,dw,dh);
}

$('copyBtn').addEventListener('click',async()=>{
  const t=$('summaryText');t.focus();t.select();
  try{await navigator.clipboard.writeText(t.value);$('saveStatus').textContent='Summary copied.';}
  catch(e){try{document.execCommand('copy');$('saveStatus').textContent='Summary copied.';}catch(e2){$('saveStatus').textContent='Select the text below and copy it.';}}
});

$('saveBtn').addEventListener('click',()=>{
  if(!lastResult)return;
  const cv=$('cardCanvas');
  const safe=(state.name||'planner').replace(/[^a-z0-9]+/gi,'-').toLowerCase();
  cv.toBlob(blob=>{
    if(!blob){$('saveStatus').textContent='Could not create the image. Take a screenshot instead.';return;}
    const url=URL.createObjectURL(blob);
    const a=document.createElement('a');a.href=url;a.download=`hexland-${safe}-${lastResult.date}.png`;document.body.appendChild(a);a.click();a.remove();
    setTimeout(()=>URL.revokeObjectURL(url),2000);
    $('saveStatus').textContent='Saved. Send the PNG to your teacher.';
  },'image/png');
});

// teacher verification
$('vBtn').addEventListener('click',()=>{
  const n=$('vName').value,d=$('vDate').value.trim(),s=parseInt($('vScore').value,10);
  if(!n||!d||isNaN(s)){$('vOut').textContent='Enter the name, date and score exactly as printed on the card.';return;}
  const out=[];
  for(const mode of ['iso','real'])for(const win of [true,false])out.push(`${mode==='iso'?'Isotropic plain':'River valley'}, ${win?'win':'loss'}: ${verifyCode(n,d,mode,win,s)}`);
  $('vOut').innerHTML='A genuine card with those details shows one of these codes:<br>'+out.join('<br>');
});

// initial paint behind the start dialog
startGame('', 'iso');
})();
