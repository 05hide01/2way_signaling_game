git # 2way_signaling_game
import numpy as np
import random as rand
import math
import csv
import pprint


#実際の各粒の数
rnv=10000;
rm=200;
reh=400;         rel=200;
rma=6000;        rmp=4000;
#予想の粒の数
pmh=[100];         pml=[100];
pnvh=[10000];       pnvl=[10000];
peh=[100];         pel=[50];
#信号aに対すa,p
pmaa=[5000];        pmpa=[5000];
#信号pに対すa,p
pmap=[5000];        pmpp=[5000];
#U系の計算でのp-r倍率、p系を使うときはすべての値にこれを掛ける
def p_r(pnv):
    p_r=rnv/pnv;
    return p_r;
#ph*に掛けるもの、Advanced攻撃は1,primary攻撃は0.6
winratep=1.0;
#a,pタイプで変化する各数値
Rbp=140;        Rba=280;
Caa=140;        Cap=90;
Lba=180;        Lbp=90;
Lha=190;        Lhp=100;
Rha=270;        Rhp=220;
Lvi_Pvi=np.array([[2,3,6,4],[0.04,0.08,0.06,0.12]]);
Lv=np.array([2,5]);
#define function of calculate Lvi*Pvi
def Lv_Pv(mp,ma):
    ma_p=[mp,ma];
    summa_p=sum(ma_p);
    #LP=[ma/summa_p,mp/summa_p]
    res_LP=Lv*ma_p/summa_p;
    return res_LP;
#h,lタイプで変化する各数値
alphh=0.8;      alphl=0.4;
#変えるかも系
CDD=[20,10,0];       CAD=[30,20,0];
#(θd=h,wd=h),(θd=h,wd=l),(θd=l,wd=h),(θd=l,wd=l)
epsi=[0.04,0.045,0.05,0.035]
#awa,awp,pwa,pwp
lamb=[10,12,16,18];
#これは10か100でやってみる
La=1000;          Lp=1800;
#avCAD,way0のUa計算用
avCADa=(CAD[2]+CAD[1])/2;
avCADp=(CAD[2]+CAD[0])/2;
#avpma,avpmp,way0のUd計算用
def avpma(n):
    avpma=pmaa[n]+pmpa[n];
    return avpma
def avpmp(n):
    avpmp=pmap[n]+pmpp[n];
    return avpmp
#確率に基づいてタイプを特定するための関数
def possi(possibility_type1,possibility_type2):
    val_list=[0,1];
    weight_list=[possibility_type1,possibility_type2];
    val=rand.choices(val_list,weights=weight_list)[0];
    return val;
#sigma計算関数
def sigmaf2(nv,e,m,L,epsi):
    result = 0;
    for i in range(1,m):
        result =result + ((math.comb(m,i))*(math.comb(int(nv-m-epsi*e),L-i)))/(math.comb(nv,L));
    return result;

#define f1,f2
def f1(nv,e,L,epsi):
    f1=(math.comb(int(nv-epsi*e),L))/(math.comb(nv,L));
    return f1;
#define function of calculate Pb*
def calPB(f1,sigf,nv,e,alph,m,L,epsi,lamb):
    PB=(1-f1(nv,e,L,epsi))*(1-((1-alph)/lamb))+sigf(nv,e,m,L,epsi)*(alph/lamb);
    return PB;
#define function of calculate Ph*
def calPh(nv,e,m,L,epsi,lamb,sigf):
    Ph=sigf(nv,e,m,L,epsi)*(1-(1/lamb));
    return Ph;
#define function of calculate SDC
def calSDC(nv,e,m,Lh,LP,L,epsi,lamb,sigf):
    res_SDC=Lh*sigf(nv,e,m,L,epsi)*(1-(1/lamb))*np.sum(LP);
    return res_SDC;
#define function of calculate SPB
def calSPB(f1, sigf, nv, e, alph, m, Rb, L,epsi,lamb):
    PB_val=calPB(f1, sigf, nv, e, alph, m, L,epsi,lamb)
    res_SPB=Rb*PB_val;
    return res_SPB
#define function of calculate AR
def calAR(Rh,nv,e,m,Lh,LP,L,epsi,lamb,sigf):
    AR=Rh*sigf(nv,e,m,L,epsi)*(1-(1/lamb))*np.sum(LP);
    return AR;
#define function of calculate AL
def calAL(Lb,f1,sigf,nv,e,alph,m,L,epsi,lamb):
    AL=Lb*calPB(f1,sigf,nv,e,alph,m,L,epsi,lamb);
    return AL;
#define function of calculate Cd
def calCd(e,alph,m):
    Cd=e+0.5*m*(1-alph)+m*alph;
    return Cd;
#define function of calculate Ua
def calcUa(Ca,CAD,Lh,LP,Rh,Lb,f1,sigf,nv,e,alph,m,L,epsi,lamb):
    Ua=calAR(Rh,nv,e,m,Lh,LP,L,epsi,lamb,sigf)-Ca-calAL(Lb,f1,sigf,nv,e,alph,m,L,epsi,lamb)-CAD;
    return Ua;
#define function of calculate Ud
def calcUd(CDD,Lh,LP,Rb,f1,sigf,nv,e,alph,m,L,epsi,lamb):
    Ud=calSPB(f1,sigf,nv,e,alph,m,Rb,L,epsi,lamb)-calCd(e,alph,m)-CDD-calSDC(nv,e,m,Lh,LP,L,epsi,lamb,sigf);
    return Ud;
#正しい粒の数でUa,Ud,Ph*を求める
rUd=[];rUa=[];Phstar=[];
#攻撃成功率のph*を求めるこれは攻撃の成功失敗判定に使う
#ph*(θD,wd,θA)=ph*(1,1,1)
Phstar.append(calPh(rnv,reh,rm,La,epsi[0],(lamb[0]+lamb[1])/2,sigmaf2))
#ph*(θD,wd,θA)=ph*(1,1,0)
Phstar.append(winratep*calPh(rnv,reh,rm,Lp,epsi[0],(lamb[2]+lamb[3])/2,sigmaf2))
#ph*(θD,wd,θA)=ph*(1,0,1)
Phstar.append(calPh(rnv,reh,rm,La,epsi[1],(lamb[0]+lamb[1])/2,sigmaf2))
#ph*(θD,wd,θA)=ph*(1,0,0)
Phstar.append(winratep*calPh(rnv,reh,rm,Lp,epsi[1],(lamb[2]+lamb[3])/2,sigmaf2))
#ph*(θD,wd,θA)=ph*(0,1,1)
Phstar.append(calPh(rnv,rel,rm,La,epsi[2],(lamb[0]+lamb[1])/2,sigmaf2))
#ph*(θD,wd,θA)=ph*(0,1,0)
Phstar.append(winratep*calPh(rnv,rel,rm,Lp,epsi[2],(lamb[2]+lamb[3])/2,sigmaf2))
#ph*(θD,wd,θA)=ph*(0,0,1)
Phstar.append(calPh(rnv,rel,rm,La,epsi[3],(lamb[0]+lamb[1])/2,sigmaf2))
#ph*(θD,wd,θA)=ph*(0,0,0)
Phstar.append(winratep*calPh(rnv,rel,rm,Lp,epsi[3],(lamb[2]+lamb[3])/2,sigmaf2))
#defender_type,attacker_type
θd=[];      θa=[];
#最初のθDのタイプを決める
θd.append(possi(0.5,0.5));
print('θd=%d'%θd[0])

#rud,rua
rud00=calcUd(CDD[2],Lha,Lv_Pv(rmp,rma),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,epsi[0],(lamb[0]+lamb[1])/2)
rud01=calcUd(CDD[2],Lhp,Lv_Pv(rmp,rma),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,epsi[0],(lamb[2]+lamb[3])/2)
rud02=calcUd(CDD[0],Lha,Lv_Pv(rmp,rma),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,epsi[1],(lamb[0]+lamb[1])/2)
rud03=calcUd(CDD[0],Lhp,Lv_Pv(rmp,rma),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,epsi[1],(lamb[2]+lamb[3])/2)
rud04=calcUd(CDD[1],Lha,Lv_Pv(rmp,rma),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,epsi[2],(lamb[0]+lamb[1])/2)
rud05=calcUd(CDD[1],Lhp,Lv_Pv(rmp,rma),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,epsi[2],(lamb[2]+lamb[3])/2)
rud06=calcUd(CDD[2],Lha,Lv_Pv(rmp,rma),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,epsi[3],(lamb[0]+lamb[1])/2)
rud07=calcUd(CDD[2],Lhp,Lv_Pv(rmp,rma),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,epsi[3],(lamb[2]+lamb[3])/2)
rud0=[rud00,rud01,rud02,rud03,rud04,rud05,rud06,rud07]
rud10=calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(rmp,rma),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0])
rud11=calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(rmp,rma),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])
rud12=calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(rmp,rma),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1])
rud13=calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(rmp,rma),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])
rud14=calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(rmp,rma),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2])
rud15=calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(rmp,rma),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])
rud16=calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(rmp,rma),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3])
rud17=calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(rmp,rma),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])
rud1=[rud10,rud11,rud12,rud13,rud14,rud15,rud16,rud17]
rua00=calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,reh,alphh,rm,La,epsi[0],(lamb[0]+lamb[1])/2)
rua01=calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,epsi[0],(lamb[2]+lamb[3])/2)
rua02=calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,reh,alphh,rm,La,epsi[1],(lamb[0]+lamb[1])/2)
rua03=calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,epsi[1],(lamb[2]+lamb[3])/2)
rua04=calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,rel,alphl,rm,La,epsi[2],(lamb[0]+lamb[1])/2)
rua05=calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,epsi[2],(lamb[2]+lamb[3])/2)
rua06=calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,rel,alphl,rm,La,epsi[3],(lamb[0]+lamb[1])/2)
rua07=calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,epsi[3],(lamb[2]+lamb[3])/2)
rua0=[rua00,rua01,rua02,rua03,rua04,rua05,rua06,rua07]
rua10=calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0])
rua11=calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])
rua12=calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1])
rua13=calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])
rua14=calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2])
rua15=calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])
rua16=calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3])
rua17=calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])
#game
#UaとUdをいれるlist
Ua0=[];      Ud0=[];
Ua1=[];      Ud1=[];
RUa=[];      RUd=[];
#site_number=00~07;,10~17
site_0_num=[];      site_1_num=[];
#攻撃成功したかどうかhit=(win=1,lose=0)
hit=[]
#resetからの回数
recount=0; 
#resetする、しない
reset=0;
#前回戦略をリセットした回
ind_re=0;
#戻すときの回
ba_ind=0;
# ロジスティック関数を定義
def logistic(x, a, k, x0):
    y = k / (1 + np.exp(-a * (x - x0)))
    return y
#game
i=0;
with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
        writer = csv.writer(f)
        writer.writerow(['n','site0','hit','rUa','rUd'])
while i<5:
    i+=1;
    n=0;
    while n<500:
        recount+=1;
        rep=logistic(recount*0.2,1,1,5)
        print('recount=%d'%recount);
        reset=possi(1-rep,rep)
        if n>=1:
            hit.append(possi(1-Phstar[site_0_num[n-1]],Phstar[site_0_num[n-1]]));
            if hit[n-1]==1:
                if np.logical_or(site_0_num[n-1] == 0, site_0_num[n-1] == 4).any():
                    pmh.append(pmh[n-1]+10)
                    peh.append(peh[n-1])
                    pnvh.append(pnvh[n-1]+120)
                    pml.append(pml[n-1])
                    pel.append(pel[n-1])
                    pnvl.append(pnvl[n-1])
                    if reset==1 or recount>=50:
                        ba_ind=rand.randint(ind_re,n-1);
                        pmaa.append(pmaa[ba_ind])
                        pmpa.append(pmpa[ba_ind])
                        pmap.append(pmap[ba_ind])
                        pmpp.append(pmpp[ba_ind])
                        recount=0;
                        ind_re=n;
                    elif reset==0 and recount<50 :
                        if np.logical_or(site_1_num[n-1] == 0, site_1_num[n-1] == 4):
                            pmaa.append(pmaa[n-1]+48)
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 2, site_1_num[n-1] == 6):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+28)
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 1, site_1_num[n-1] == 5):
                            pmaa.append(pmaa[n-1]+40)
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 3, site_1_num[n-1] == 7):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+20)
                            pmpp.append(pmpp[n-1])
                elif np.logical_or(site_0_num[n-1] == 1, site_0_num[n-1] == 5).any():
                    pmh.append(pmh[n-1]+14)
                    peh.append(peh[n-1])
                    pnvh.append(pnvh[n-1]+160)
                    pml.append(pml[n-1])
                    pel.append(pel[n-1])
                    pnvl.append(pnvl[n-1])
                    if reset==1 or recount>=50:
                        ba_ind=rand.randint(ind_re,n-1);
                        pmaa.append(pmaa[ba_ind])
                        pmpa.append(pmpa[ba_ind])
                        pmap.append(pmap[ba_ind])
                        pmpp.append(pmpp[ba_ind])
                        recount=0;
                        ind_re=n;
                    elif reset==0 and recount<50 :
                        if np.logical_or(site_1_num[n-1] == 0, site_1_num[n-1] == 4):
                            pmaa.append(pmaa[n-1]+48)
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 2, site_1_num[n-1] == 6):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+28)
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 1, site_1_num[n-1] == 5):
                            pmaa.append(pmaa[n-1]+40)
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 3, site_1_num[n-1] == 7):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+20)
                            pmpp.append(pmpp[n-1])
                elif np.logical_or(site_0_num[n-1] == 2, site_0_num[n-1] == 6).any():
                    pmh.append(pmh[n-1])
                    peh.append(peh[n-1])
                    pnvh.append(pnvh[n-1])
                    pml.append(pml[n-1]+10)
                    pel.append(pel[n-1])
                    pnvl.append(pnvl[n-1]+120)
                    if reset==1 or recount>=50:
                        ba_ind=rand.randint(ind_re,n-1);
                        pmaa.append(pmaa[ba_ind])
                        pmpa.append(pmpa[ba_ind])
                        pmap.append(pmap[ba_ind])
                        pmpp.append(pmpp[ba_ind])
                        recount=0;
                        ind_re=n;
                    elif reset==0 and recount<50 :
                        if np.logical_or(site_1_num[n-1] == 0, site_1_num[n-1] == 4):
                            pmaa.append(pmaa[n-1]+48)
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 2, site_1_num[n-1] == 6):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+28)
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 1, site_1_num[n-1] == 5):
                            pmaa.append(pmaa[n-1]+40)
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 3, site_1_num[n-1] == 7):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+20)
                            pmpp.append(pmpp[n-1])
                elif np.logical_or(site_0_num[n-1] == 3, site_0_num[n-1] == 7).any():
                    pmh.append(pmh[n-1])
                    peh.append(peh[n-1])
                    pnvh.append(pnvh[n-1])
                    pml.append(pml[n-1]+18)
                    pel.append(pel[n-1])
                    pnvl.append(pnvl[n-1]+200)
                    if reset==1 or recount>=50:
                        ba_ind=rand.randint(ind_re,n-1);
                        pmaa.append(pmaa[ba_ind])
                        pmpa.append(pmpa[ba_ind])
                        pmap.append(pmap[ba_ind])
                        pmpp.append(pmpp[ba_ind])
                        recount=0;
                        ind_re=n;
                    elif reset==0 and recount<50 :
                        if np.logical_or(site_1_num[n-1] == 0, site_1_num[n-1] == 4):
                            pmaa.append(pmaa[n-1]+48)
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 2, site_1_num[n-1] == 6):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+28)
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 1, site_1_num[n-1] == 5):
                            pmaa.append(pmaa[n-1]+40)
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 3, site_1_num[n-1] == 7):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+20)
                            pmpp.append(pmpp[n-1])
            elif hit[n-1]==0:
                if np.logical_or(site_0_num[n-1] == 0, site_0_num[n-1] == 4).any():
                    pmh.append(pmh[n-1])
                    peh.append(peh[n-1]+16)
                    pnvh.append(pnvh[n-1]+200)
                    pml.append(pml[n-1])
                    pel.append(pel[n-1])
                    pnvl.append(pnvl[n-1])
                    if reset==1 or recount>=50:
                        ba_ind=rand.randint(ind_re,n-1);
                        pmaa.append(pmaa[ba_ind])
                        pmpa.append(pmpa[ba_ind])
                        pmap.append(pmap[ba_ind])
                        pmpp.append(pmpp[ba_ind])
                        recount=0;
                        ind_re=n;
                    elif reset==0 and recount<50 :
                        if np.logical_or(site_1_num[n-1] == 0, site_1_num[n-1] == 4):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1]+72)
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 2, site_1_num[n-1] == 6):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+40)
                        elif np.logical_or(site_1_num[n-1] == 1, site_1_num[n-1] == 5):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1]+52)
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 3, site_1_num[n-1] == 7):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1]+28)
                elif np.logical_or(site_0_num[n-1] == 1, site_0_num[n-1] == 5).any():
                    pmh.append(pmh[n-1])
                    peh.append(peh[n-1]+10)
                    pnvh.append(pnvh[n-1]+120)
                    pml.append(pml[n-1])
                    pel.append(pel[n-1])
                    pnvl.append(pnvl[n-1])
                    if reset==1 or recount>=50:
                        ba_ind=rand.randint(ind_re,n-1);
                        pmaa.append(pmaa[ba_ind])
                        pmpa.append(pmpa[ba_ind])
                        pmap.append(pmap[ba_ind])
                        pmpp.append(pmpp[ba_ind])
                        recount=0;
                        ind_re=n;
                    elif reset==0 and recount<50 :
                        if np.logical_or(site_1_num[n-1] == 0, site_1_num[n-1] == 4):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1]+72)
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 2, site_1_num[n-1] == 6):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+40)
                        elif np.logical_or(site_1_num[n-1] == 1, site_1_num[n-1] == 5):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1]+52)
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 3, site_1_num[n-1] == 7):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1]+28)
                elif np.logical_or(site_0_num[n-1] == 2, site_0_num[n-1] == 6).any():
                    pmh.append(pmh[n-1])
                    peh.append(peh[n-1])
                    pnvh.append(pnvh[n-1])
                    pml.append(pml[n-1])
                    pel.append(pel[n-1]+18)
                    pnvl.append(pnvl[n-1]+200)
                    if reset==1 or recount>=50:
                        ba_ind=rand.randint(ind_re,n-1);
                        pmaa.append(pmaa[ba_ind])
                        pmpa.append(pmpa[ba_ind])
                        pmap.append(pmap[ba_ind])
                        pmpp.append(pmpp[ba_ind])
                        recount=0;
                        ind_re=n;
                    elif reset==0 and recount<50 :
                        if np.logical_or(site_1_num[n-1] == 0, site_1_num[n-1] == 4):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1]+72)
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 2, site_1_num[n-1] == 6):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+40)
                        elif np.logical_or(site_1_num[n-1] == 1, site_1_num[n-1] == 5):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1]+52)
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 3, site_1_num[n-1] == 7):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1]+28)
                elif np.logical_or(site_0_num[n-1] == 3, site_0_num[n-1] == 7).any():
                    pmh.append(pmh[n-1])
                    peh.append(peh[n-1])
                    pnvh.append(pnvh[n-1])
                    pml.append(pml[n-1])
                    pel.append(pel[n-1]+8)
                    pnvl.append(pnvl[n-1]+100)
                    if reset==1 or recount>=50:
                        ba_ind=rand.randint(ind_re,n-1);
                        pmaa.append(pmaa[ba_ind])
                        pmpa.append(pmpa[ba_ind])
                        pmap.append(pmap[ba_ind])
                        pmpp.append(pmpp[ba_ind])
                        recount=0;
                        ind_re=n;
                    elif reset==0 and recount<50 :
                        if np.logical_or(site_1_num[n-1] == 0, site_1_num[n-1] == 4):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1]+72)
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 2, site_1_num[n-1] == 6):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1]+40)
                        elif np.logical_or(site_1_num[n-1] == 1, site_1_num[n-1] == 5):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1]+52)
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1])
                        elif np.logical_or(site_1_num[n-1] == 3, site_1_num[n-1] == 7):
                            pmaa.append(pmaa[n-1])
                            pmpa.append(pmpa[n-1])
                            pmap.append(pmap[n-1])
                            pmpp.append(pmpp[n-1]+28)
            #θd=1,Dhでway0
            if θd[n]==1:
                #way0のゲームを解く
                #Udの送る信号を決める
                #θd=1,wd=1,θa=a,p
                tm_1_Ud=[calcUd(CDD[2],Lha,Lv_Pv(avpmp(n-1),avpma(n-1)),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,epsi[0],(lamb[0]+lamb[1])/2),calcUd(CDD[2],Lhp,Lv_Pv(avpmp(n-1),avpma(n-1)),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,epsi[0],(lamb[2]+lamb[3])/2)]
                #θd=1,wd=0,θa=a,p
                tm_2_Ud=[calcUd(CDD[0],Lha,Lv_Pv(avpmp(n-1),avpma(n-1)),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,epsi[1],(lamb[0]+lamb[1])/2),calcUd(CDD[0],Lhp,Lv_Pv(avpmp(n-1),avpma(n-1)),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,epsi[1],(lamb[2]+lamb[3])/2)]
                min_1_Ud=min(tm_1_Ud)
                min_2_Ud=min(tm_2_Ud)
                #θaのタイプを決める
                if min_1_Ud >= min_2_Ud:
                    #wd=1,hの信号に対してa,pどっちにするか
                    tm_Ua=[calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,epsi[0],(lamb[0]+lamb[1])/2),calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,epsi[0],(lamb[2]+lamb[3])/2)]
                    Ua0.append(max(tm_Ua))
                    Ud0.append(tm_1_Ud[np.argmax(tm_Ua)])
                    RUa.append(rua0[np.argmax(tm_Ua)])
                    RUd.append(rud0[np.argmax(tm_Ua)])
                    site_0_num.append(np.argmax(tm_Ua))
                    θa.append(np.argmax(tm_Ua))
                    with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
                        writer = csv.writer(f)
                        writer.writerow([n,site_0_num[n],hit[n-1],RUa[n],RUd[n]])
                    #way1のゲームを解く
                    #θaの送る信号を決める
                    if θa[n]==1:
                        #a=1,aの時にa,pどっちの信号を送るかsite_0_num.append(np.argmax(tm_Ua)+6)
                        #a=1,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[0]),calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[0])]
                        #a=1,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[1]),calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[1])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,aの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_num.append(np.argmax(tm_Ud))
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+2)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                    elif θa[n]==0:
                        #a=0,pの時にa,pどっちの信号を送るか
                        #a=0,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                        #a=0,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+4)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+6)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                #θaのタイプを決める
                elif min_1_Ud < min_2_Ud:
                    #wd=0,lの信号に対してa,pどっちにするか
                    tm_Ua=[calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,epsi[1],(lamb[0]+lamb[1])/2),calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,epsi[1],(lamb[2]+lamb[3])/2)]
                    Ua0.append(max(tm_Ua))
                    Ud0.append(tm_1_Ud[np.argmax(tm_Ua)])
                    site_0_number=np.argmax(tm_Ua)
                    site_0_num.append(site_0_number+2)
                    RUa.append(rua0[site_0_num[n]])
                    RUd.append(rud0[site_0_num[n]])
                    θa.append(np.argmax(tm_Ua))
                    with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
                        writer = csv.writer(f)
                        writer.writerow([n,site_0_num[n],hit[n-1],RUa[n],RUd[n]])
                    #way1のゲームを解く
                    #θaの送る信号を決める
                    if θa[n]==1:
                        #a=1,aの時にa,pどっちの信号を送るか
                        #a=1,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[0]),calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[0])]
                        #a=1,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[1]),calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[1])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,aの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_num.append(np.argmax(tm_Ud))
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+2)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                    elif θa[n]==0:
                        #a=0,pの時にa,pどっちの信号を送るか
                        #a=0,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                        #a=0,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+4)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+6)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
            #θd=0,Dlでway0
            elif θd[n]==0:
                #way0のゲームを解く
                #Udの送る信号を決める
                #θd=0,wd=1,θa=a,p
                tm_1_Ud=[calcUd(CDD[1],Lha,Lv_Pv(avpmp(n-1),avpma(n-1)),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,epsi[2],(lamb[0]+lamb[1])/2),calcUd(CDD[1],Lhp,Lv_Pv(avpmp(n-1),avpma(n-1)),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,epsi[2],(lamb[2]+lamb[3])/2)]
                #θd=0,wd=0,θa=a,p
                tm_2_Ud=[calcUd(CDD[2],Lha,Lv_Pv(avpmp(n-1),avpma(n-1)),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,epsi[3],(lamb[0]+lamb[1])/2),calcUd(CDD[2],Lhp,Lv_Pv(avpmp(n-1),avpma(n-1)),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,epsi[3],(lamb[2]+lamb[3])/2)]
                min_1_Ud=min(tm_1_Ud)
                min_2_Ud=min(tm_2_Ud)
                #θaのタイプを決める
                if min_1_Ud >= min_2_Ud:
                    #wd=1,hの信号に対してa,pどっちにするか
                    tm_Ua=[calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,epsi[2],(lamb[0]+lamb[1])/2),calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,epsi[2],(lamb[2]+lamb[3])/2)]
                    Ua0.append(max(tm_Ua))
                    Ud0.append(tm_1_Ud[np.argmax(tm_Ua)])
                    site_0_number=np.argmax(tm_Ua)
                    site_0_num.append(site_0_number+4)
                    RUa.append(rua0[site_0_num[n]])
                    RUd.append(rud0[site_0_num[n]])
                    θa.append(np.argmax(tm_Ua))
                    with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
                        writer = csv.writer(f)
                        writer.writerow([n,site_0_num[n],hit[n-1],RUa[n],RUd[n]])
                    #way1のゲームを解く
                    #θaの送る信号を決める
                    if θa[n]==1:
                        #a=1,aの時にa,pどっちの信号を送るか
                        #a=1,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[0]),calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1]),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[0]))]
                        #a=1,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[1]),calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[1])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,aの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_num.append(np.argmax(tm_Ud))
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+2)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                    elif θa[n]==0:
                        #a=0,pの時にa,pどっちの信号を送るか
                        #a=0,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                        #a=0,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+4)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+6)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                #θaのタイプを決める
                elif min_1_Ud < min_2_Ud:
                    #wd=0,lの信号に対してa,pどっちにするか
                    tm_Ua=[calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,epsi[3],(lamb[0]+lamb[1])/2),calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,epsi[3],(lamb[2]+lamb[3])/2)]
                    Ua0.append(max(tm_Ua))
                    Ud0.append(tm_1_Ud[np.argmax(tm_Ua)])
                    site_0_number=np.argmax(tm_Ua)
                    site_0_num.append(site_0_number+6)
                    RUa.append(rua0[site_0_num[n]])
                    RUd.append(rud0[site_0_num[n]])
                    θa.append(np.argmax(tm_Ua))
                    with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
                        writer = csv.writer(f)
                        writer.writerow([n,site_0_num[n],hit[n-1],RUa[n],RUd[n]])
                    #way1のゲームを解く
                    #θaの送る信号を決める
                    if θa[n]==1:
                        #a=1,aの時にa,pどっちの信号を送るか
                        #a=1,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[0]),calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[0])]
                        #a=1,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[1]),calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[1])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,aの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_num.append(np.argmax(tm_Ud))
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+2)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                    elif θa[n]==0:
                        #a=0,pの時にa,pどっちの信号を送るか
                        #a=0,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                        #a=0,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+4)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+6)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
        elif n==0:
            #θd=1,Dhでway0
            if θd[n]==1:
                #way0のゲームを解く
                #Udの送る信号を決める
                #θd=1,wd=1,θa=a,p
                tm_1_Ud=[calcUd(CDD[2],Lha,Lv_Pv(avpmp(n-1),avpma(n-1)),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,epsi[0],(lamb[0]+lamb[1])/2),calcUd(CDD[2],Lhp,Lv_Pv(avpmp(n-1),avpma(n-1)),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,epsi[0],(lamb[2]+lamb[3])/2)]
                #θd=1,wd=0,θa=a,p
                tm_2_Ud=[calcUd(CDD[0],Lha,Lv_Pv(avpmp(n-1),avpma(n-1)),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,epsi[1],(lamb[0]+lamb[1])/2),calcUd(CDD[0],Lhp,Lv_Pv(avpmp(n-1),avpma(n-1)),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,epsi[1],(lamb[2]+lamb[3])/2)]
                min_1_Ud=min(tm_1_Ud)
                min_2_Ud=min(tm_2_Ud)
                #θaのタイプを決める
                if min_1_Ud >= min_2_Ud:
                    #wd=1,hの信号に対してa,pどっちにするか
                    tm_Ua=[calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,epsi[0],(lamb[0]+lamb[1])/2),calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,epsi[0],(lamb[2]+lamb[3])/2)]
                    Ua0.append(max(tm_Ua))
                    Ud0.append(tm_1_Ud[np.argmax(tm_Ua)])
                    RUa.append(rua0[np.argmax(tm_Ua)])
                    RUd.append(rud0[np.argmax(tm_Ua)])
                    site_0_num.append(np.argmax(tm_Ua))
                    θa.append(np.argmax(tm_Ua))
                    with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
                        writer = csv.writer(f)
                        writer.writerow([n,site_0_num[n],RUa[n],RUd[n]])
                    #way1のゲームを解く
                    #θaの送る信号を決める
                    if θa[n]==1:
                        #a=1,aの時にa,pどっちの信号を送るか
                        #a=1,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[0]),calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[0])]
                        #a=1,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[1]),calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[1])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,aの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_num.append(np.argmax(tm_Ud))
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+2)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                    elif θa[n]==0:
                        #a=0,pの時にa,pどっちの信号を送るか
                        #a=0,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                        #a=0,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+4)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+6)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                #θaのタイプを決める
                elif min_1_Ud < min_2_Ud:
                    #wd=0,lの信号に対してa,pどっちにするか
                    tm_Ua=[calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,epsi[1],(lamb[0]+lamb[1])/2),calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,epsi[1],(lamb[2]+lamb[3])/2)]
                    Ua0.append(max(tm_Ua))
                    Ud0.append(tm_1_Ud[np.argmax(tm_Ua)])
                    site_0_number=np.argmax(tm_Ua)
                    site_0_num.append(site_0_number+2)
                    RUa.append(rua0[site_0_num[n]])
                    RUd.append(rud0[site_0_num[n]])
                    θa.append(np.argmax(tm_Ua))
                    with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
                        writer = csv.writer(f)
                        writer.writerow([n,site_0_num[n],RUa[n],RUd[n]])
                    #way1のゲームを解く
                    #θaの送る信号を決める
                    if θa[n]==1:
                        #a=1,aの時にa,pどっちの信号を送るか
                        #a=1,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[0]),calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[0])]
                        #a=1,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[1]),calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[1])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,aの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_num.append(np.argmax(tm_Ud))
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+2)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                    elif θa[n]==0:
                        #a=0,pの時にa,pどっちの信号を送るか
                        #a=0,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                        #a=0,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+4)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+6)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
            #θd=0,Dlでway0
            elif θd[n]==0:
                #way0のゲームを解く
                #Udの送る信号を決める
                #θd=0,wd=1,θa=a,p
                tm_1_Ud=[calcUd(CDD[1],Lha,Lv_Pv(avpmp(n-1),avpma(n-1)),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,epsi[2],(lamb[0]+lamb[1])/2),calcUd(CDD[1],Lhp,Lv_Pv(avpmp(n-1),avpma(n-1)),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,epsi[2],(lamb[2]+lamb[3])/2)]
                #θd=0,wd=0,θa=a,p
                tm_2_Ud=[calcUd(CDD[2],Lha,Lv_Pv(avpmp(n-1),avpma(n-1)),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,epsi[3],(lamb[0]+lamb[1])/2),calcUd(CDD[2],Lhp,Lv_Pv(avpmp(n-1),avpma(n-1)),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,epsi[3],(lamb[2]+lamb[3])/2)]
                min_1_Ud=min(tm_1_Ud)
                min_2_Ud=min(tm_2_Ud)
                #θaのタイプを決める
                if min_1_Ud >= min_2_Ud:
                    #wd=1,hの信号に対してa,pどっちにするか
                    tm_Ua=[calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,epsi[2],(lamb[0]+lamb[1])/2),calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,epsi[2],(lamb[2]+lamb[3])/2)]
                    Ua0.append(max(tm_Ua))
                    Ud0.append(tm_1_Ud[np.argmax(tm_Ua)])
                    site_0_number=np.argmax(tm_Ua)
                    site_0_num.append(site_0_number+4)
                    RUa.append(rua0[site_0_num[n]])
                    RUd.append(rud0[site_0_num[n]])
                    θa.append(np.argmax(tm_Ua))
                    with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
                        writer = csv.writer(f)
                        writer.writerow([n,site_0_num[n],RUa[n],RUd[n]])
                    #way1のゲームを解く
                    #θaの送る信号を決める
                    if θa[n]==1:
                        #a=1,aの時にa,pどっちの信号を送るか
                        #a=1,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[0]),calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1]),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[0]))]
                        #a=1,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[1]),calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[1])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,aの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_num.append(np.argmax(tm_Ud))
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+2)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                    elif θa[n]==0:
                        #a=0,pの時にa,pどっちの信号を送るか
                        #a=0,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                        #a=0,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+4)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+6)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                #θaのタイプを決める
                elif min_1_Ud < min_2_Ud:
                    #wd=0,lの信号に対してa,pどっちにするか
                    tm_Ua=[calcUa(Caa,avCADa,Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,epsi[3],(lamb[0]+lamb[1])/2),calcUa(Cap,avCADp,Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,epsi[3],(lamb[2]+lamb[3])/2)]
                    Ua0.append(max(tm_Ua))
                    Ud0.append(tm_1_Ud[np.argmax(tm_Ua)])
                    site_0_number=np.argmax(tm_Ua)
                    site_0_num.append(site_0_number+6)
                    RUa.append(rua0[site_0_num[n]])
                    RUd.append(rud0[site_0_num[n]])
                    θa.append(np.argmax(tm_Ua))
                    with open('C:/卒業研究/卒業研究/logistic_50_1000_1.csv','a') as f:
                        writer = csv.writer(f)
                        writer.writerow([n,site_0_num[n],RUa[n],RUd[n]])
                    #way1のゲームを解く
                    #θaの送る信号を決める
                    if θa[n]==1:
                        #a=1,aの時にa,pどっちの信号を送るか
                        #a=1,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[0]),calcUa(Caa,CAD[2],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[0])]
                        #a=1,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),La,(epsi[0]+epsi[1])/2,lamb[1]),calcUa(Caa,CAD[1],Lha,Lv_Pv(rmp,rma),Rha,Lba,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),La,(epsi[2]+epsi[3])/2,lamb[1])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,aの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[0]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[0])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_num.append(np.argmax(tm_Ud))
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,reh,alphh,rm,La,(epsi[0]+epsi[1])/2,lamb[1]),calcUd((CDD[0]+CDD[1])/2,Lha,Lv_Pv(pmpp[n-1],pmap[n-1]),Rba,f1,sigmaf2,rnv,rel,alphl,rm,La,(epsi[2]+epsi[3])/2,lamb[1])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+2)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                    elif θa[n]==0:
                        #a=0,pの時にa,pどっちの信号を送るか
                        #a=0,wa=1,θd=h,l
                        tm_1_Ua=[calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUa(Cap,CAD[0],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                        #a=0,wa=0,θd=h,l
                        tm_2_Ua=[calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(peh[n-1]*p_r(pnvh[n-1])),alphh,int(pmh[n-1]*p_r(pnvh[n-1])),Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUa(Cap,CAD[2],Lhp,Lv_Pv(rmp,rma),Rhp,Lbp,f1,sigmaf2,rnv,int(pel[n-1]*p_r(pnvl[n-1])),alphl,int(pml[n-1]*p_r(pnvl[n-1])),Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                        max_1_Ua=max(tm_1_Ua)
                        max_2_Ua=max(tm_2_Ua)
                        #θdのタイプを決める
                        if max_1_Ua >= max_2_Ua:
                            #wa=1,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[2]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[2])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+4)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
                        elif max_1_Ua < max_2_Ua:
                            ##wa=0,pの信号に対してh,lどっちにするか
                            tm_Ud=[calcUd((CDD[0]+CDD[2])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,reh,alphh,rm,Lp,(epsi[0]+epsi[1])/2,lamb[3]),calcUd((CDD[0]+CDD[1])/2,Lhp,Lv_Pv(pmpa[n-1],pmaa[n-1]),Rbp,f1,sigmaf2,rnv,rel,alphl,rm,Lp,(epsi[2]+epsi[3])/2,lamb[3])]
                            Ud1.append(max(tm_Ud))
                            Ua1.append(tm_1_Ua[np.argmax(tm_Ud)])
                            site_1_number=np.argmax(tm_Ud)
                            site_1_num.append(site_1_number+6)
                            θd.append(np.argmax(tm_Ud))
                            print('n=%d'%n);print('θa=%d,θd=%d'%(θa[n],θd[n]));print('Ua0=%d,Ud0=%d'%(Ua0[n-1],Ud0[n-1]));print('pmh=%d,peh=%d,pnvh=%d'%(pmh[n],peh[n],pnvh[n]));print('pml=%d,pel=%d,pnvl=%d'%(pml[n],pel[n],pnvl[n]))
                            print('pmaa=%d,pmpa=%d,pmap=%d,pmpp=%d'%(pmaa[n],pmpa[n],pmap[n],pmpp[n]));print('site0=%d,site1=%d'%(site_0_num[n],site_1_num[n]));print('possi=%f'%possi(1-Phstar[site_0_num[n]],Phstar[site_0_num[n]]));n+=1;
