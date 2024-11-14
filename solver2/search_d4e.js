/* Dist4: 28.54 GB in 16 parts 
   p01 = 70*2187*782*16  16 = (10 of 11 et bits = 1024) / 4 configs/byte / 16 parts
   p02 = p01*2, p03 = p01*3, etc
*/
const p01 = 1915462080,  p02 = 3830924160,  p03 = 5746386240,  p04 = 7661848320;
const p05 = 9577310400,  p06 = 11492772480, p07 = 13408234560, p08 = 15323696640;
const p09 = 17239158720, p10 = 19154620800, p11 = 21070082880, p12 = 22985544960;
const p13 = 24901007040, p14 = 26816469120, p15 = 28731931200;

function solver_search(epn, etn, cpn, ctn, cp6cn, eprn, n, mvlist)
{
  for (var i=0, mv=0; (mv=mvlist[i]) != -1; i++) {
    if (done > 0 || gdone[0] == 1)
      return;
    count[0]++;
    var ep = ep_mov[epn*18+mv];
    var et = et_mov[etn*18+mv];
    var cp = cp_mov[cpn*18+mv];
    var ct = ct_mov[ctn*18+mv];
    if (n == depth) {
      count[1]++;
      if (ep == 0 && et == 0 && cp == 0 && ct == 0) {
        count[2]++;
        var cp6c = cp6c_mov[cp6cn*18+mv];
        var cpr = cp6c_cpr[cp6c];
        var epr = new Uint8Array(3);
        get_epr_mov2(epr, epn, eprn, mv);
        seq[n] = mv;
        if (chk_sol(cpr, epr))
          return;
        var ix = cpr*13824 + eprsum(epr);
        var dst = distp2[ix];
        if (dst < 9) {
          if (n + dst < minmv) {
            minmv = dst + n;
            sol3c[0] = n;
            for (var j=1; j <= n; j++)
              sol3c[j] = seq[j];
            depth2 = dst;
            if (use_p2seq) 
              get_p2_seq(cpr, eprsum(epr));
            else
              solver_search2 (0, 0, 0, 0, cp6c, epr, 1, mvlist2);
            done2 = 0;
          }
        }
      }
    }
    else {
      var ix = ept_op_idx[ep];
      if (ix != -1) 
        var op = ept_min_op[ix*2048+et];
      else
        op = ep_min_op[ep];
      var epmin = ep_min[ep];
      var etsym = get_etsym(ep, et, op);
      if (ix != -1) {
        var ix2 = ept_ops_ix2[ept_ops_ix1[epmin]*2048+etsym];
        if (ix2 != -1) {
          if (depth >= gdone[1]) {
            done = 2;
            return;
          }
          op = get_min_op_3c(cp, ct, op, ix2);
          var time1 = Date.now();
          if ((time1-stime0)/1000 >= stl) {
            if (minmv == 99) {
              if (auto_extend_search == 0) {
                auto_extend_search = 1;
                stl_msg(2);
              }
            }
            else {
              if (auto_extend_search == 0)
                stl_msg(1);
              done = 1;
            }
          }
        }
      }
      var cpsym = cp_sym[cp*48+op];
      if (CT_SYM_METHOD == 3)
        var ctsym = get_ctsym(cpsym, ct, op);
      else {
        var cpt = cp*2187 + ct;
        var ctsym = get_ctsym(cpt, op);
      }
      if (depth-n <= 11 && depth-n >= 9) {  // depth=18, n=7, prune with 12
        var rs = etsym>>1;
        ix = (cpsym*2187+ctsym)*200192 + epmin*256 + (rs>>2);  // MIN_EP*256 = 200192 
        tmp = (ix < p08) ?
          ((ix < p04) ? 
            ((ix < p02) ? 
              ((ix < p01) ? dist401[ix]     : dist402[ix-p01]) :
              ((ix < p03) ? dist403[ix-p02] : dist404[ix-p03])) :
            ((ix < p06) ? 
              ((ix < p05) ? dist405[ix-p04] : dist406[ix-p05]) :
              ((ix < p07) ? dist407[ix-p06] : dist408[ix-p07]))) :
          ((ix < p12) ?
            ((ix < p10) ? 
              ((ix < p09) ? dist409[ix-p08] : dist410[ix-p09]) :
              ((ix < p11) ? dist411[ix-p10] : dist412[ix-p11])) :
            ((ix < p14) ? 
              ((ix < p13) ? dist413[ix-p12] : dist414[ix-p13]) :
              ((ix < p15) ? dist415[ix-p14] : dist416[ix-p15])));
        tmp = (tmp>>((rs&3)<<1))&3;
        dist = (tmp) ? tmp+9+n : 0;
        // d4a++;
        if (dist > depth) {
          // d4b++;
          continue;
        }
      }
      if (depth-n <= 10 && depth-n >= 8) {
        ix = epmin*1119744 + ctsym*512 + (etsym>>2);  // C_TWIST*512 = 1119744
        var tmp = ((dist3[ix]>>((etsym&3)<<1))&3);
        dist = (tmp) ? tmp+8+n : 0;
        if (dist > depth)
          continue;
      }
      if (depth-n <= 9) {
        ix = epmin*76580 + cpsym*1094 + (ctsym>>1);  // C_PRM*1094 = 76580
        var dist = n + ((ctsym&1) ? dist1[ix]>>4 : dist1[ix]&0xF);
        if (dist > depth) 
          continue;
        ix = epmin*71680 + cpsym*1024 + (etsym>>1);  // C_PRM*1024 = 71680
        dist = n + ((etsym&1) ? dist2[ix]>>4 : dist2[ix]&0xF);
        if (dist > depth) 
          continue;
      }
      var cp6c = cp6c_mov[cp6cn*18+mv];
      if (minmv-n <= 10) {
        ix = cp6c*1094 + (ct>>1);
        dist = n + ((ct&1) ? dist5[ix]>>4 : dist5[ix]&0xF);
        if (dist >= minmv)
          continue;
      }
      var epr = new Uint8Array(3);
      get_epr_mov2(epr, epn, eprn, mv);
      if (USE_DIST9 && minmv-n <= 7) {
        ix = cp6c_cpr[cp6c]*13824 + eprsum(epr);
        if (dist9[ix] + n >= minmv)
          continue;
      }
      if (ep == 0 && et == 0 & cp == 0 && ct == 0) {
        ix = cp6c_cpr[cp6c]*13824 + eprsum(epr);
        if (distp2[ix] + n > depth)
          continue;
      }
      seq[n] = mv;
      solver_search(ep, et, cp, ct, cp6c, epr, n+1, seq_gen[mv]);
    }
  }
}
