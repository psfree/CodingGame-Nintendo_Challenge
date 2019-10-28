#include <iostream>
#include <iomanip>
#include <vector>
#include <cstring>
#include <algorithm>

using namespace std;

void printmat(char ** mat, int m, int n) {
	for(int z=0; z<m; z++){
			for(int q=0; q<n; q++) {
				printf("%01d", ((char (*)[n])mat)[z][q]);
			}
			printf("\n");
		}

}

void gg2rref(char ** mat, int m, int n) {
	int i=0;
	int j=0;
	
	//mat[m][n]
	while( i<m && j<n) {
		int ind=-1;
		for(int q=i; q<m; q++) {
			if(((char (*)[n])mat)[q][j] == 1) {
				ind = q;
				break;
			}
		}
		if(ind == -1) {
			j++;
			continue;
		}
		char tmp[n-j];
		for(int z = j; z<n; z++) {
			tmp[z-j] = ((char (*)[n])mat)[ind][z];
			((char (*)[n])mat)[ind][z] = ((char (*)[n])mat)[i][z];
			((char (*)[n])mat)[i][z] = tmp[z-j];
		}
		
		char tcol[m];
		for(int z=0; z<m; z++)
			tcol[z] = ((char (*)[n])mat)[z][j];
		tcol[i] = 0;
		
		char flip[m][n-j];
		memset(flip, 0, sizeof(flip));
		for(int x=0; x<m; x++) {
			if(tcol[x] == 1) {
				memcpy(flip[x], tmp, n-j);
			}
		}
		
		for(int z =0; z<m; z++) {
			for(int q=j; q<n; q++) {
				((char (*)[n])mat)[z][q] ^=  flip[z][q-j];
			}
		
		}
		i++;
		j++;
		
	
	}

}


class polynomial {
	#define SIZEMAX 1024
	private:
	public:
		int top_bit;
		bool irreduce;
		int mSize;
		char * bits;
		polynomial * div;
		unsigned int * arr;
		bool squared;
		
		void print() {
			int sz = mSize;
			if(sz % 32 != 0) {
				sz = ((sz/32) +1)*32;
			}
			for(int i = 0 ; i< sz/32; i++) {
				printf("%08x", arr[i]);
				if((i+1) < sz/32)
					printf(" ");
			}
		
		}
		
		vector<polynomial> * bka() {
			int top = this->top_bit;
			char mat[top][top];
			int tmp = sizeof(mat);
			memset(mat, 0, sizeof(mat));
			char ingen[SIZEMAX*2] = {};
			for(int j=0; j<SIZEMAX*2; j++) {
				ingen[j]=0;
			}
			ingen[0]=1;
			for(int i=0; i< top; i++) {
				polynomial x(top*2, ingen);
				polynomial v = x/(*this);
				for(int j=0; j<top; j++){
					mat[i][j] = v.bits[j];
				}
				ingen[2*(i+1)] = 1;
				ingen[2*i] = 0;
			}
			char Imat[top][top];
			memset(Imat, 0, sizeof(Imat));
			for(int i=0; i<top; i++)
				Imat[i][i]=1;
			char Mmat[top][top];
			for(int i=0; i<top; i++) {
				for(int j=0; j<top; j++) {
					Mmat[i][j] = mat[i][j]^Imat[i][j];
				}
			}

			char flippy[top][2*top+2];
			memset(flippy, 0, sizeof(flippy));
			char rImat[top][top];
			memset(rImat, 0, sizeof(rImat));
			for(int w=0; w<top; w++) {
				rImat[w][top-1-w] = 1;
			}
			char rMmat[top][top];
			for(int w=0; w<top; w++)
				for(int x=0; x<top; x++)
					rMmat[w][x] = Mmat[w][top-1-x];
			for(int w=0; w<top; w++) {
				flippy[w][0] = 0;
				memcpy(&flippy[w][1], rMmat[w], top);
				flippy[w][top+1]=0;
				memcpy(&flippy[w][top+2], rImat[w], top);
			} 
			
			
			gg2rref((char **)flippy, top, 2*top+2);
			vector<polynomial> null;
			for(int w=0; w<top; w++) {
				int x;
				for(x=0; x<top+1; x++) {
					if(flippy[w][x]!=0)
						break;
				}
				if(x==top+1) {
					char bits[top];
					int count=0;
					for(int x=2*top+1; x>top+1; x--) {
						bits[count++] = flippy[w][x];
					}
					polynomial p(top, bits);
					if( !(p.top_bit==0 && p.arr[0]==1)) //exclude trivial solution
						null.push_back(p);
				}
			
			}
			vector<polynomial> * known = new vector<polynomial>();
			known->push_back(*this);
			
			for(int i =0; i< null.size(); i++) {
				polynomial nv = null.at(i);
				polynomial gc = GCD(*this, nv);
				polynomial newfac = *(((*this)/gc).div);
				int sz = known->size();
				for(int j=0; j<sz; j++) {
					polynomial t = known->at(j)/newfac;
					if(t.top_bit==0 && t.arr[0]==0) {
						polynomial q = *(t.div);
						known->at(j) = newfac;
						known->push_back(q);
						break;
					}
				}
			
			
			}
			if(this->squared) {
				for(int i=0; i<known->size(); i++)
					known->at(i).squared = 1;
			
			}
			return known;
		
		}
		
		static bool sortPairs(vector<polynomial> a, vector<polynomial> b) {
			bool ret = a.at(0).reverse() < b.at(0).reverse();
			return ret;
		}
		
		
		//this function is in alpha testing
		vector<vector<polynomial> > * centauri() {
			vector<polynomial> * irr = this->factor();
			int sz = irr->size();
			for(int i=0; i<sz; i++) {
				polynomial p = irr->at(i);
				if(p.squared) {
					p.squared = false;
					irr->at(i) = p;
					irr->push_back(p);
				}
			}
			sz = irr->size();
			int total = (1<<sz) -1;
			char bits[1];
			bits[0] = 1;
			vector<vector<polynomial> > * out= new vector<vector<polynomial> >();
			for(int i=1; i<total; i++) {
				polynomial a(1 ,bits);
				polynomial b(1, bits);
				for(int j=0; j<sz; j++) {
					int sel = i>>j &1;
					if(sel) {
						a = a*irr->at(j);
					}
					else {
						b = b*irr->at(j);
					}
				
				}

				if(a.top_bit < (this->mSize/2)) {
					if(b.top_bit < (this->mSize/2)) {
						vector<polynomial> vec;
						vec.push_back(a);
						vec.push_back(b);
						out->push_back(vec);
						}
				}
			
			}
			
			for(vector< vector<polynomial> >::iterator it = out->begin(); it != out->end(); ++it) {
				polynomial p = (*it).at(0);
				for(vector< vector<polynomial> >::iterator ip = out->begin(); ip!=out->end(); ++ip) {
					if(ip==it)
						continue;
					if(p==(*ip).at(0)) {
						out->erase(ip);
					
					}
				}
			
			}
			
			//add corner case
			if(this->top_bit < this->mSize/2) {
				char bit[1];
				bit[0] = 1;
				polynomial one(1, bit);
				polynomial self(32, this->bits);
				
				vector<polynomial> p1, p2;
				p1.push_back(self);
				p1.push_back(one);
				
				p2.push_back(one);
				p2.push_back(self);
				
				out->push_back(p1);
				out->push_back(p2);
			
			}
			sort(out->begin(), out->end(), sortPairs);
			
			return out;
			
		}
		
		vector<polynomial> * factor() {
			vector<polynomial> * out = this->sff();
			while(true) {
				int sz = out->size();
				int icount =0;
				int dcount = 0;
				vector<polynomial> round = *out;
				for(int i=0; i<sz; i++ ){
					polynomial f = round.at(i);
					if(f.irreduce) {
						icount++;
						continue;
					}
					vector<polynomial> * fac = f.bka();
					if(fac->size() == 1) {
						fac->at(0).irreduce = true;
					}
					out->insert(out->end(), fac->begin(), fac->end());
					out->erase(out->begin()+i -dcount++);
				}
				if(icount==sz)
					break;		
			
			}
			return out;
		}
		
		polynomial reverse() {
			polynomial p(*this);
			for(int i=0; i<mSize/16; i++) {
				p.arr[i] = this->arr[mSize/16-1-i];
			}
			p.updateBits();
			return p;
		}
		
		vector<polynomial> * sff() {
			polynomial df = this->derivative();
			if(df.top_bit == 0 && df.bits[0] ==0) {
				polynomial srt = this->sqrt();
				vector<polynomial> * vsrt = srt.sff();
				//double elements to square
				int init_size = vsrt->size();
				for(int i=0; i< init_size; i++) {
					vsrt->at(i).squared =1;
				}
				return vsrt;
			}
			polynomial g = polynomial::GCD(*this, df);
			if(!(g.arr[0]==1 && g.top_bit == 0)) {  //g is not equal to one
				//g is a factor of input polynomial
				
				polynomial h = *((*this/g).div);

				
				vector<polynomial> * vg = g.sff();
				vector<polynomial> * vh = h.sff();
				for(int i = 0; i< vh->size(); i++)
					vg->push_back(vh->at(i));
				delete vh;
				return vg;
			}else {
				vector<polynomial> * factors = new vector<polynomial>();
				factors->push_back(*this);
				return factors;
			}
		
		}
		
		polynomial derivative() {
			polynomial t;
			t = *this;
			int top=0;
			for(int i = SIZEMAX*2 -1; i>0; i--) {
				if(i%2==1) {
					t.bits[i-1]=t.bits[i];
					t.bits[i] = 0;
					if( (i-1)>top && t.bits[i-1]==1 )
						top=i-1;
				}
			}
			t.top_bit = top;
			t.updateArray();
			return t;
		}
		
		polynomial sqrt() {
			polynomial t;
			t=*this;
			char * bits = new char[SIZEMAX*2];
			for(int i =0; i<SIZEMAX*2; i++)
				bits[i] = 0;
			for(int i = t.top_bit; i >-1; i--) {
				if(i%2==1 && t.bits[i] == 1) {
					printf("error odd degree sqrt\n");
				}
				else if(i%2==0) {
					bits[i/2] = t.bits[i];
				}
			}
			delete t.bits;
			t.bits = bits;
			t.top_bit = t.top_bit/2;
			t.updateArray();
			return t;
		}
		
		polynomial operator *(const polynomial& b) const {
			if(this->top_bit == 0) {
				if(this->bits[0] ==0) {
					return *this; //zero already
				}else {
					return b;	//its 1 so its just the whatever its multiplied by
				}
			}else {
				char bits[SIZEMAX*2];
				memset(bits, 0, SIZEMAX*2);
				for(int i=0; i<this->top_bit+1; i++) {
					if(this->bits[i]==1) {
						for(int j=0; j<b.top_bit+1; j++) {
							bits[i+j] ^= b.bits[j];
						}
					}
				}
				int top = this->top_bit + b.top_bit+1;
				return polynomial(top, bits);
			
			}
		
		}
				
		polynomial operator /(const polynomial& b) const {
			polynomial t;
			t = *this;
			polynomial out = t;
			char dbits[SIZEMAX*2];
			memset(dbits, 0, SIZEMAX*2);
			int diff = 0;
			int ind=1;
			int maxdiff= out.top_bit - b.top_bit;
			if(maxdiff<0)
				maxdiff = 0;
			while(true) {
				diff = out.top_bit - b.top_bit;
				if(diff <0) {
					out.div = new polynomial(maxdiff+1, dbits);
					return out;
				}
				dbits[diff] = 1;
				out = out^(b << diff);
				ind++;
				
			}
		}
		
		polynomial& operator =(const polynomial& b) {
			if(this != &b) {
				unsigned int * arr = new unsigned int[SIZEMAX/16];
				char * bits = new char[SIZEMAX*2];
				memcpy(arr, b.arr, sizeof(unsigned int)*SIZEMAX/16);
				memcpy(bits, b.bits, SIZEMAX*2);
				this->arr = arr;
				this->bits = bits;
				this->mSize = b.mSize;
				this->top_bit = b.top_bit;
				this->squared = b.squared;
				this->irreduce = b.irreduce;
				if(b.div!=NULL) {
					delete this->div;
					this->div = new polynomial(*b.div);
				}
				else {
					this->div = NULL;
				}
			}
			return *this;	
		}
		
		polynomial operator ^(const polynomial& n) const {
			polynomial t;
			t=*this;
			int top=0;
			for(int i = 0; i< SIZEMAX*2; i++) {
				t.bits[i] ^=n.bits[i];
				if(t.bits[i])
					top=i;
			}
			t.updateArray();
			t.top_bit = top;
			t.mSize = top;
			return t;
		}
		
		polynomial operator >>(int b) const {
			polynomial t(*this);
			if(b==0)
				return t;
			char * tbits = new char[SIZEMAX*2];
			int top_bit =0;
			int i;
			for(i=SIZEMAX*2-1; i>b-1; i--) {
				tbits[i-b] = t.bits[i];
				if(t.bits[i]==1)
					top_bit=i-b;
			}
			delete t.bits;
			t.bits = tbits;
			t.top_bit=top_bit;
			t.mSize +=b;
			t.updateArray();
			return t;
		}
		
		polynomial operator <<(int b) const {
			polynomial t(*this);
			if(b==0)
				return t;
			char * tbits = new char[SIZEMAX*2];
			int top_bit =0;
			int i;
			for(i=0; i<SIZEMAX*2-b; i++) {
				tbits[i+b] = t.bits[i];
				if(t.bits[i]==1)
					top_bit=i+b;
			}
			for(; i<SIZEMAX*2; i++)
				tbits[i] = 0;
			for(i=0; i<b; i++)
				tbits[i]=0;
			delete t.bits;
			t.bits = tbits;
			t.top_bit=top_bit;
			t.mSize +=b;
			t.updateArray();
			return t;
		}
	
	
		bool operator >=(const polynomial b) const {
			bool gt = *this>b;
			bool eq = *this==b;
			return gt || eq;
		}
	
		bool operator <=(const polynomial b) const {
			bool lt = *this<b;
			bool eq = *this==b;
			return lt || eq;
		}
	
		bool operator !=(const polynomial b) const {
			return !(*this==b);
		}
	
		bool operator ==(const polynomial b) const {
			if(this->top_bit!=b.top_bit) {
				return false;
			}
			else {
				int index = this->top_bit-1;
				while(index>-1) {
					if(this->bits[index] != b.bits[index]) {
						return false;
					}
					index--;
				}
				return true;
			}
		}
	
		bool operator >(const polynomial b) const {
			if(this->top_bit > b.top_bit) {
				return true;
			}
			else if(this->top_bit==b.top_bit){
				int index = this->top_bit-1;
				while(index>-1) {
					if(this->bits[index] >b.bits[index]) {
						return true;
					}
					else if(this->bits[index] < b.bits[index]) {
						return false;
					}
					index--;
				}
		
			}
			return false;
		}
	
		bool operator <(const polynomial b) const {
			if(this->top_bit < b.top_bit) {
				return true;
			}
			else if(this->top_bit==b.top_bit) {
				int index = this->top_bit - 1;
				while(index >-1) {
					if(this->bits[index] < b.bits[index]) {
						return true;
					}
					else if(this->bits[index]>b.bits[index]) {
						return false;
					}
					index--;
				}
			}
			//equal or gt
			return false;
		}	
		
		static polynomial GCD(polynomial p, polynomial q) {
			polynomial a = p;
			polynomial b = q;
			polynomial r ;
			while(true) {
				r = a/b;
				if(r.top_bit == 0) {
					if(r.bits[0] ==0)
						return b;
					else
						return r;
				}
				a = b;
				b = r;
			}
		}
	
		void updateArray() {
			for(int i=0; i< SIZEMAX/16; i++) {
				arr[i] = 0;
			}
			for(int i=0; i< SIZEMAX*2; i++) {
				arr[i/32] |= bits[i] << (i%32);
			}
		}
	
		void updateBits() {
			for(int i=0; i< SIZEMAX*2; i++) {
				bits[i] = 0;
			}
			for(int i=0; i< SIZEMAX*2; i++) {
				bits[i] = (arr[i/32] >> (i %32) &1);
				if(bits[i] == 1)
					top_bit = i;
			}
	
		}
	
		polynomial(int size, char * s) {
			mSize = size;
			squared = false;
			irreduce = false;
			div=NULL;
			arr = new unsigned int[SIZEMAX/16];
			bits = new char[SIZEMAX*2];
			memset(bits, 0, SIZEMAX*2);
			for(int x=0; x<size; x++) {
				bits[x] = s[x];
			}
			updateArray();
			for(int i=mSize-1; i>-1; i--) {
				if(bits[i]==1) {
					top_bit = i;
					break;
				}
			}
		}
	
		polynomial(int size, unsigned int * in) {
			mSize = size;
			squared = false;
			irreduce = false;
			div=NULL;
			arr = new unsigned int[SIZEMAX/16];
			for (int i = 0; i < SIZEMAX / 16; i++) {
				if(i<size/32)
					arr[i] = in[i];
				else
					arr[i]=0;
			}
			bits = new char[SIZEMAX*2];
			for(int i=0; i< SIZEMAX*2; i++) {
				if(i<mSize)
					bits[i] = (in[i/32] >> (i %32) &1);
				else
					bits[i] = 0;
			}
			for(int i=mSize; i>-1; i--) {
				if(bits[i]==1) {
					top_bit = i;
					break;
				}
			}
		}
		
		polynomial() {
			div=NULL;
			irreduce=false;
			squared = false;
			mSize = 0;
			arr = new unsigned int[SIZEMAX/16];
			bits = new char[SIZEMAX*2];
			top_bit=0;
		}
	
		polynomial(const polynomial &p) {
			mSize = p.mSize;
			irreduce = p.irreduce;
			squared = p.squared;
			top_bit = p.top_bit;
			if(p.div!=NULL)
				div = new polynomial(*p.div);
			else
				div = NULL;
			arr = new unsigned int[SIZEMAX/16];
			memcpy(arr, p.arr, sizeof(unsigned int)*SIZEMAX/16);
			bits = new char[SIZEMAX*2];
			memcpy(bits, p.bits, SIZEMAX*2);
		}
		~polynomial(){
			if(div!=NULL)
				delete div;
			delete bits;
			delete arr;
		}

};

//int * modolo(char * a, char * b, int sz) {
//}

int main()
{
  int size;

  cin >> size;

  unsigned int* a = new unsigned int[size / 16]; // <- input tab to encrypt
 
  for (int i = 0; i < size / 16; i++) {   // Read size / 16 integers to a
    cin >> hex >> a[i];
  } 
 polynomial p(size*2, a);
 vector<vector<polynomial> > * decrypt = p.centauri();
 for(int i=0; i<decrypt->size(); i++) {
		decrypt->at(i).at(0).print();
		printf(" ");
		decrypt->at(i).at(1).print();
		printf("\n");		
  }

 /* 
    Good luck humans     
 */
  return 0;
}
