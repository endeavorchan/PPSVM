#include "randpool.h"
#include "rsa.h"
#include "hex.h"
#include "files.h"
#include <iostream>
#include "osrng.h"      // AutoSeededRandomPool
#include "dh.h"
#include <cmath>
#include"modarith.h"//模运算的一个头文件

#define  COL  25
#define ROW 219

#define AR  207
#define HTSIZE  4099
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <ctime>

#include "secblock.h"
using CryptoPP::SecByteBlock;
#include <hex.h>
using CryptoPP::HexEncoder;
#include <string>
using std::string;
#include "nbtheory.h"
using CryptoPP::ModularExponentiation;


using namespace std;
using namespace CryptoPP;
 
#pragma comment(lib, "cryptlib.lib")


//函数声明以及一些全局变量的初始化
AutoSeededRandomPool rng;
Integer  Sk;
Integer  Pk;
Integer p("36F0255DDE973DCB3B399D747F23E32ED6FDB1F77598338BFDF44159C4EC64DDAEB5F78671CBFB22"
                "106AE64C32C5BCE4CFD4F5920DA0EBC8B01ECA9292AE3DBA1B7A4A899DA181390BB3BD1659C81294"
                "F400A3490BF9481211C79404A576605A5160DBEE83B4E019B6D799AE131BA4C23DFF83475E9C40FA"
                "6725B7C9E3AA2C6596E9C05702DB30A07C9AA2DC235C5269E39D0CA9DF7AAD44612AD6F88F696992"
                "98F3CAB1B54367FB0E8B93F735E7DE83CD6FA1B9D1C931C41C6188D3E7F179FC64D87C5D13F85D70"
                "4A3AA20F90B3AD3621D434096AA7E8E7C66AB683156A951AEA2DD9E76705FAEFEA8D71A575535597"
                "0000000000000001H");
//我们使用http://www.cryptopp.com/fom-serve/cache/71.html 中推荐的一个2048bits的大安全素数(但其实是248Bytes的一个素数，这一点可在rand_SN_gen(void)代码中发现！
ModularArithmetic group_S(p);  
Integer rand_SN_gen(void);//在0~p-1的范围内生成随机数的函数
Integer g=rand_SN_gen();//随机生成生成子

bool Encryption_ElGamal( Integer m,Integer *M1,Integer *G1);//加密函数声明
bool Decryption_ElGamal( Integer *result,Integer M1,Integer G1);//解密函数声明

void HashtableCreat();
Integer SearchHT(Integer W);
int ZQGS=0;//统计正确预测的个数
 int main()
 {
	 while(g==1||g==0)
         g=rand_SN_gen();
//cout<<g<<endl;
g=group_S.Exponentiate(g,2);
//cout<<g<<endl;

 clock_t start, finish; 
    double   duration; 

   HashtableCreat();
 
  Integer **matrix;
  Integer	  *value_of_y;
matrix = new Integer *[ROW];
value_of_y=new Integer[ROW];
 
double dsv[ROW][COL];
double dalpha[ROW];
double k=0.0;
char *ppp=NULL;
int jjjj=0;
int num=1;
char   buff[1024*3]; 
ofstream outr("result1029t2",ios::trunc);
ifstream  Bobdata("RL1027m",ios::in);

while(!Bobdata.eof()) 
             { 
                Bobdata.getline(buff, 1024*3); 
			  	 ppp= strtok(buff," ");
                dalpha[jjjj]=atof(ppp);
			cout<<dalpha[jjjj]<<endl;
				int i=0;
				 for( i=0;i<COL;i++)
				 {
				 ppp=strtok(NULL,":");
				 num=atoi(ppp);
                  ppp=strtok(NULL," ");
				  	while(i!=num-1)
				  {dsv[jjjj][i]=0.0;i++;}
				  if(i==num-1)
				      dsv[jjjj][i]=atof(ppp);
				 }
				 jjjj++;
           } 
Bobdata.close();

// Reading file Finished****************

Sk=rand_SN_gen(); // THE SECRET KEY
Pk=group_S.Exponentiate(g,Sk);//THE PUBLIC KEY
//cout<<"SK::::"<<Sk<<'\n'<<"PK::::"<<Pk<<endl;


jjjj=0;
double Data_of_Alice[AR][COL];
int Label_of_Alice[AR];
ifstream  Alicedata("RL1029t",ios::in);


while(!Alicedata.eof()) 
                  { 
                Alicedata.getline(buff, 1024*3); 
			  	 ppp= strtok(buff," ");
                 Label_of_Alice[jjjj]=atoi(ppp);
			//	cout<<dalpha[jjjj]<<endl;
				int i=0;
				 for( i=0;i<COL;i++)
				 {
				 ppp=strtok(NULL,":");
				 num=atoi(ppp);
                  ppp=strtok(NULL," ");
				  	while(i!=num-1)
				  {Data_of_Alice[jjjj][i]=0.0;i++;}
				  if(i==num-1)
				      Data_of_Alice[jjjj][i]=atof(ppp);
				 }
				 jjjj++;
                  } 
Alicedata.close();


double sum1=0.0;

Integer *Exp_Matrix=new Integer[COL*COL];
for(int i=0;i<COL;i++)
     for(int j=i;j<COL;j++)
	 { 
		 sum1=0.0;
		 for(int k=0;k<ROW;k++)
		 {
	          		sum1=sum1+dalpha[k]*dsv[k][i]*dsv[k][j];
		 }
	       Exp_Matrix[i*COL+j]=(Integer)(10000*sum1);
		  cout<<Exp_Matrix[i*COL+j]<<endl;
	 }

///////////////////////////////////////////////////////////////

for(int ggg=0;ggg<AR;ggg++)
{

start=clock();
	Integer *XX_M,*XX_G;
XX_M=new Integer[COL*COL];// Alice 的数据经加密后形成的N*N的密文C向量
XX_G=new Integer[COL*COL];// Alice 的数据经加密后形成的N*N的密文G向量
Integer *XX_Cyuan;
XX_Cyuan=new Integer[COL*COL];
for(int i=0;i<COL;i++)
   for(int j=i;j<COL;j++)
   {
	   Integer m=(Integer)(100000000*Data_of_Alice[ggg][i]*Data_of_Alice[ggg][j]);
	    XX_Cyuan[COL*i+j]=m/1000000;
	//	cout<<XX_Cyuan[COL*i+j]<<endl;
       Encryption_ElGamal( XX_Cyuan[COL*i+j], XX_M+COL*i+j, XX_G+COL*i+j);
   }

Integer SUMInter("0");
Integer  WM(1);
Integer  WG(1);
Integer  para(1);
Integer  para2(1);
finish=clock();
 duration = (double)(finish - start) / CLOCKS_PER_SEC; 
 cout<<"加密时间:"<<duration<<"seconds   ";
//outr<<"加密时间:"<<duration<<"seconds   ";
start=clock();
for(int i=0;i<COL;i++)
   for(int j=i;j<COL;j++)
   {
	   Integer  AYY;
	   if(i!=j)
		    AYY=Exp_Matrix[i*COL+j]*2;
	   else
		   AYY=Exp_Matrix[i*COL+j];
        SUMInter=SUMInter+AYY*XX_Cyuan[COL*i+j];
		 if(AYY>=0)
         para=group_S.Exponentiate(*(XX_M+COL*i+j),AYY);
		 else
		 { para2=-AYY; para=group_S.Exponentiate(*(XX_M+COL*i+j),para2);  para=group_S.Divide(1,para);}
		 WM=group_S.Multiply(WM,para);
		if(AYY>=0)
		 para=group_S.Exponentiate(*(XX_G+COL*i+j),AYY);
		else
		{ para2=-AYY; para=group_S.Exponentiate(*(XX_G+COL*i+j),para2);  para=group_S.Divide(1,para);} 
         WG=group_S.Multiply(WG,para);
   }
//  cout<<"10_20:   "<<SUMInter;

	   Integer *w_result=new Integer(1);
       Decryption_ElGamal( w_result, WM, WG);
finish=clock();
	   duration = (double)(finish - start) / CLOCKS_PER_SEC; 
	   cout<<" 运算时间: "<<duration<<"seconds  ";
	  // 	outr<<" 运算时间: "<<duration<<"seconds  ";
//	   cout<<WM<<endl;
//cout<<*w_result<<endl;

 	 
	   start=clock();
	   Integer   hashr= SearchHT(*w_result);
//   cout<<hashr<<endl;
   finish=clock();
   cout<< " HTMIM离散对数时间:"<<(double)(finish - start) / CLOCKS_PER_SEC<<endl;
 //  outr<< " HTMIM离散对数时间:"<<(double)(finish - start) / CLOCKS_PER_SEC<<endl;
 //  	 Integer b("-558944");
//	   Integer b("-3754");
 Integer b("0");
	   Integer kkk1=b+1;
	   Integer kkk2=b-1;
	   int kkk3=0;
	   Integer para3=hashr;
	   if(para3>b)
	   { 
		   //  cout<<ggg+1<<":+1 "; 
	      // outr<<ggg+1<<":+1 ";
		   cout<<ggg+1<<":0"<<endl; 
		    outr<<"0"<<endl; 
			if(Label_of_Alice[ggg]==0)
				ZQGS++;
	   }
	   else
	   {
	   // cout<<ggg+1<<":-1 ";
	   //outr<<ggg+1<<":-1 ";
	   	   cout<<ggg+1<<":1"<<endl; 
		    outr<<"1"<<endl; 
			if(Label_of_Alice[ggg]==1)
				ZQGS++;
	   }
   cout<<para3<<"距离:"<<para3-b<<"  "<<endl;
//	   outr<<para3<<"距离:"<<para3-b<<"  "<<endl;

}
cout<<ZQGS<<endl;
outr.close();
//free(matrix);
//free(value_of_y);
return 0;
 }
 
 
bool Encryption_ElGamal( Integer m,Integer *M1,Integer *G1)
{
	AutoSeededRandomPool rng1;
	Integer rand_ri=rand_SN_gen();
	Integer var(1);
 //    cout<<rand_ri<<endl;
	 Integer c01(1);
	if(m<0)
	{
		var=-m;
	c01=group_S.Exponentiate(g,var);
	 c01=group_S.Divide(1,c01);
	}
	else
        c01=group_S.Exponentiate(g,m);
	 Integer c02=group_S.Exponentiate(Pk,rand_ri);
	 Integer c03=group_S.Multiply(c01,c02);
     Integer g1=group_S.Exponentiate(g,rand_ri);
    *M1=c03;
	*G1=g1;
	return true;
}

bool Decryption_ElGamal( Integer *result,Integer M1,Integer G1)
{
	 Integer r1=group_S.Exponentiate(G1,Sk);
     *result=group_S.Divide(M1,r1);
	 return true;
	 }
	
Integer rand_SN_gen(void)
{
	   Integer kk=0;
	do{
		kk=0;
	byte randomBytes[248];
	AutoSeededRandomPool asrp1;
     asrp1.GenerateBlock(randomBytes, 248);
   int k;
   for(k=0;k<=247;k++)
      kk=Integer(randomBytes[k])+kk*256;
	}
	while(kk>p);
//	cout<<kk<<endl;
//	cout<<p<<endl;
   Integer mm= group_S.ConvertIn(kk);
   return mm;
}

Integer HT1_elem_gm[HTSIZE];
int HT1_elem_m[HTSIZE];
int HT1_elem_flag[HTSIZE]={0};
Integer HT2_elem_gm[HTSIZE];
int HT2_elem_m[HTSIZE]={-1};
int HT2_elem_flag[HTSIZE]={0};
Integer  gb0=group_S.Exponentiate(2,12);

void HashtableCreat()
{
		for(int j=0;j<4096;j++)
	{
		Integer mm1= group_S.Multiply(j,gb0);
          Integer mm2=group_S.Exponentiate(g,mm1);
	      int k=int(mm2%HTSIZE) ;
		  while(HT2_elem_flag[k]==1)
		                    k=(k+1)%HTSIZE;
		  if(HT2_elem_flag[k]==0)
		  {
		   HT2_elem_gm[k]=mm2;
		   HT2_elem_m[k]=j;
		   HT2_elem_flag[k]=1;
		  }
	}
	for(int i=-1;i>-4096;i--)
	{
		Integer mm1= group_S.Multiply(-i,gb0);
		Integer mm3=group_S.Exponentiate(g,mm1);
		Integer  mm2=group_S.Divide(1,mm3);
	      int k=int(mm2%HTSIZE) ;
		  while(HT1_elem_flag[k]==1)
		                    k=(k+1)%HTSIZE;
		  if(HT1_elem_flag[k]==0)
		  {
		   HT1_elem_gm[k]=mm2;
		   HT1_elem_m[k]=i;
		   HT1_elem_flag[k]=1;
		  }
	}



}

Integer SearchHT(Integer W)
{
	for(int j=0;j<4096;j++)
	{
		Integer mm1= group_S.Exponentiate(g,j);
		Integer  mm3=group_S.Divide(1,mm1);
          Integer  mm2=group_S.Multiply(W,mm3);
	      int k=int(mm2%HTSIZE) ;
		  while(HT2_elem_gm[k]!=mm2&&HT2_elem_flag[k+1]==1)
		                    k=(k+1)%HTSIZE;
		  if(HT2_elem_gm[k]==mm2)
		      return HT2_elem_m[k]*4096+j;
	}
	for(int i=-1;i>-4096;i--)
	{
		Integer mm1= group_S.Exponentiate(g,-i);
		Integer  mm2=group_S.Multiply(W,mm1);
	      int k=int(mm2%HTSIZE) ;
		  while(HT1_elem_gm[k]!=mm2&&HT1_elem_flag[k+1]==1)
		                    k=(k+1)%HTSIZE;
		if(HT1_elem_gm[k]==mm2) 
			return HT1_elem_m[k]*4096+i;
	}

		return 0;
}
