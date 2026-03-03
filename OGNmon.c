
#define _CRT_SECURE_NO_WARNINGS
#define _USE_32BIT_TIME_T

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <signal.h>
#include <ctype.h>
#include <fcntl.h>
#include <errno.h>
// NB. link with math library (-lm) on raspi

#ifdef WIN32
#include <io.h>
#include <conio.h>
#include <winsock2.h>
#include <ws2tcpip.h>
#define kbhit _kbhit	/* windows prefers underscore version */
#define getch _getch	/* windows prefers underscore version */
#define close _close	/* windows prefers underscore version */
//#define read _read	/* windows prefers underscore version */
// OGN APRS server details
#define OGN_SERVER "aprs.glidernet.org"
#define OGN_PORT 14580
#pragma comment(lib, "ws2_32.lib")
#else	// linux
#include <unistd.h>
#include <stddef.h>
#include <sys/time.h>	/* struct timeval, select() */
#include <termios.h>	/* tcgetattr(), tcsetattr() */
#include <stdlib.h>		/* atexit(), exit() */
#include <unistd.h>		/* read() */
#include <sys/ioctl.h>
#include <arpa/inet.h>
static int kbhit(void);	/* local version */
static int getch(void);	/* local version */
#endif

// local stn coords will be set/retrieved from conf or stn files, or Totternhoe coords until first beacon
static double stnlat = 51.8807340, stnlon = -0.5645430;
static double reclat, reclon;		// flarm record lat/lons in degrees
int use_skt = 1, sockfd = 0;

// global variables
static int bearing, alt, tim, tz, stnrep, beacontim, edat, terminate=0, redraw=0, btxt=3;
static char *gt, *comma, *fixlen, *pstn, *ident, *idcol, *cmnt;
static double pi = 3.1415926535, slat, slon, rlat, rlon;	// radians
static double range;										// km
static time_t timer, kaltim=0;
static int debug=0, bandist=0, bantax=0, banexp=0, banpas=0, banpwr=0, banpara=0, banadsb=0, paused=0;
static char sortype[16], mtyp[16], line[256], cpyline[256], linetext[256];
static int bytes_read, linelen = 0;

static void headings();				// top line & bottom 3 lines
static void prompt();				// prompt line & bottom 2 lines
static int perfsort();				// process sortype
static int procline();				// process keyboard input
static void tidy_scr();				// apply colour rules
static int kcolours();				// display/change colour codes
static char *brng_text(int brng);	// return text of bearing (NW,SW, etc)
static void set_brng(int brng,int txt,char *buf);
static int m16=1;					// use 16 point bearings text, else 8pt

// configurable colouring
// standard text colours: 31=red, 32=green, 33=yellow, 34=blue, 35=magenta, 36=cyan, 37=white, 39=default
// (38;5;nm are 256 colour pallet values, probably they should all use this)
char defcol[16] = "39;0m";		// default
char actcol[16] = "38;5;14m";	// cyan:	active <3 mins (tried "36;1" "38;5;51m" "38;5;14m")
char lowcol[16] = "32m";		// green:	active below 600ft (taxying)
char stacol[16] = "32;4m";		// green_ul:used for displaying sort type
char pascol[16] = "38;5;11m";	// yellow:	passive 3 to 10 minutes (tried "33m" "38;5;228m" "38;5;11m")
char expcol[16] = "38;5;240m";	// black:	expired >10 mins (greyed out, was 30;1 black)
char stlcol[16] = "35m";		// magenta:	active stealth
char notcol[16] = "31;1m";		// red:		active notrack (was 31m)
char discol[16] = "34;1m";		// blue:	distant (bold to make lighter)
char pasdis[16] = "38;5;194m";	// light yellow:	distant passive
// associate mnemonics with buffers
static struct colours { char *mnem, *cbuf; } colours[12] = {
	{ "defcol", defcol },
	{ "actcol", actcol },
	{ "lowcol", lowcol },
	{ "stacol", stacol },
	{ "pascol", pascol },
	{ "expcol", expcol },
	{ "stlcol", stlcol },
	{ "notcol", notcol },
	{ "discol", discol },
	{ "pasdis", pasdis },
	{ 0, 0 }
};
static char *colbuf(char *mnem);					// get col buffer ptr

// screen parameters
static int botline=45, columns=125;					// window depth and width
static int ipline=42;								// cursor resting place
static void setwindowsize(), clearlines(int frm,int upto), clearscr(), scroll(int inc);
// Header on line 1, LocStn always line 2, RemStns line 3 onwards
static int nxtlno=3, nxtstn=3, dbgline=3, scrolled=0, revscroll=0, banauto=0;

// the contents of OGNdb.txt
static struct db { char ident[8]; char cmnt[48]; struct db* nxt; } *db;
static void rd_db(), wr_db();
static struct db *exists(char *id), *new_entry(char* id,char* cmt);
static char* get_cmnt(char* ident);					// (adds db entry if requ)
static int dbowner = 1;

// components of each flarm line
// (all have 1st letter 'h' because they were hashes in perl, and now only val struct members)
static struct val {
	int hlno, hbearing, halt, htype, htim, hstat, hstnrep;
	double hrange, hlat, hlon, hprevlat, hprevlon;
	char hident[12], hmtyp[8], hstn[12], hstars[40];
	char *hcurcol, *hstarcol, *hidcol;
	char hlatlon[20];
	int hrtbrng;
	struct val *nxt;
} *val=0;
static struct val* add_val(char* id);				// add a new val struct to head of val list
static struct val* get_vptr(char *id);				// ret ptr to struct with hident==id if any
static struct val* new_val(char* id,int stnrep);	// creat a new val entry
static struct val* get_id(int lno);					// ret ptr to struct with hlno==lno
static void makeline(struct val* pv);				// make a display line from val struct (m==colour)
static void displine(struct val* pv);				// display a flarm line
static void mvdown();								// move all flarm lines down 1 place
static void dump_to_file(int m);					// add dump of flarm lines to file OGNdump.txt
static void dtfbw(void), dtfcol(void), rdrw(void);	// (fns w/o args)
static void load_config();							// load OGNmon.config
static void chk4dups();								// check for line nos used twice

// compare fns for qsort
typedef const void* cmparg;
int cmpintfn(cmparg a, cmparg b);					// integers
int cmpcharfn(cmparg a, cmparg b);					// strings
int cmpdblfn(cmparg a, cmparg b);					// doubles

// sort field descriptions
static struct sortvars { int (*cmpfn)(cmparg,cmparg); char* mnem; int fldos; } sortvars[8] = {
	{ cmpcharfn,"ident", offsetof(struct val,hident) },
	{ cmpintfn, "alt",   offsetof(struct val,halt) },
	{ cmpintfn, "brng",  offsetof(struct val,hbearing) },
	{ cmpintfn, "type",  offsetof(struct val,htype) },
	{ cmpintfn, "time",  offsetof(struct val,htim) },
	{ cmpcharfn,"col",   offsetof(struct val,hcurcol) },
	{ cmpdblfn, "range", offsetof(struct val,hrange) },
	{ 0, 0, 0 }
}, *get_sortvars(char *mnem);
static void reorder(int (*cmpfn)(cmparg,cmparg), int os);	// sort by changing line numbers

// filter types
static struct filtvars { char *mnem; int *banvar; } filtvars[8] = {
	{ "dist", &bandist },
	{ "taxy", &bantax  },
	{ "exp",  &banexp  },
	{ "pas",  &banpas  },
	{ "pwr",  &banpwr  },
	{ "para", &banpara },
	{ "adsb", &banadsb },
	{ 0, 0 }
}, *get_filtvar(char *mnem);

// mon types (the lazy way, but like the rest)
static struct dbgvars { char *mnem; int val; } dbgvars[8] = {
	{ "mon",  1 },	// only lines containing 'APRS' and no hash char or OGNDVS string
	{ "mone", 2 },	// only lines not containing 'APRS' (extra data lines)
	{ "mona", 3 },	// all lines
	{ "mons", 4 },	// all lines sent only
	{ "monc", 5 },	// all lines preceded by idle count and length in brackets
	{ "monp", 6 },	// all lines, and set pause if origin unknown
	{ 0, 0 }
}, *get_dbgvar(char *mnem);

// special characters in kbuf[0], and fns to handle their commands
static struct spchars { int c; char *cmd; void (*fn)(); } spchars[8] = {
	{ '|', "dump_to_file_bw",	&dtfbw	},
	{ '@', "dump_to_file_col",	&dtfcol	},
	{ '%', "redraw_scr",		&rdrw   },
	{ '^', "tidy_scr",			&tidy_scr },
	{ '~', "load_config",		&load_config },
	{ '>', "write_db",			&wr_db },
	{ 0, 0 }
}, *get_spitem(char *cmd);		// used to get fn for command
static char *get_spcmd(int c);	// used to get command for special char

// origin flag characters configurable in OGNmon.conf
#define MAXORI 48
static struct orichrs { char c; char stn[12]; } orichrs[MAXORI] = {
	{ '+', "UKDUN2"    },
	{ '*', "AVX949"    },
	{ 'v', "AVX913"    },
	{ 'V', "AVX1253"   },
	{ 'n', "NAVITER"   },
	{ 'N', "NAVITER2"  },
	{ 0, 0 }
};

// configurable variables
int AFH = 200;							// default airfield height in feet amsl
int APH = 400;							// default approach height amsl
int MBP = 4;							// default minutes before passive status
int MBE = 10;							// default minutes before expired status
int DST = 16;							// default distant status(km)
double RNG = 25.0;						// default range for w32 aprs login
char STN[16];							// LocStn name for WIN32 from .conf only
char w32nam[16];						// w32 stn name for aprs login and beacons

static void add_orichr(struct val* pv);	// add origin chr to pv->hstars

// report decoders
static void get_tz(), calcBRAT(char*), locstn(), locrpt(), locdat(), remstn(), remrpt();
static void dec_tim(char* s);
// calculate bearing and distance from flat/flon to rlat/rlon
static void calcBD(double flat, double flon);

static void catch_sigint(int sig) { terminate=1; }

static void* memalloc(size_t bytes);	// get some memory

// keyboard variables
static char kbuf[128];
static int kblen, hadret=0, uc(char*);
static void raw(), keyboard(), clr_kbuf(), add_to_kbuf(int c);

static void disperr(char* s) { printf("%s\nunknown %s type\n", line, s); }

#ifdef WIN32
static int setup_socket() {
	// Initialize Winsock
	WSADATA wsaData;
	int result = WSAStartup(MAKEWORD(2, 2), &wsaData);
	if (result != 0) {
		fprintf(stderr, "WSAStartup failed: %d\n", result);
		return 0;
	}
	// Create socket
	sockfd = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
	if (sockfd == INVALID_SOCKET) {
		fprintf(stderr, "Error creating socket: %d\n", WSAGetLastError());
		WSACleanup();
		return 0;
	}
	// Resolve hostname
	struct addrinfo hints, * result_addr;
	ZeroMemory(&hints, sizeof(hints));
	hints.ai_family = AF_INET;
	hints.ai_socktype = SOCK_STREAM;
	hints.ai_protocol = IPPROTO_TCP;
	printf("Resolving %s...\n", OGN_SERVER);

	char port_str[8];
	sprintf(port_str, "%d", OGN_PORT);
	if (getaddrinfo(OGN_SERVER, port_str, &hints, &result_addr) != 0) {
		fprintf(stderr, "Failed to resolve hostname\n");
		closesocket(sockfd);
		WSACleanup();
		return 0;
	}
	// Connect to OGN server
	printf("Connecting to %s:%d...\n", OGN_SERVER, OGN_PORT);
	if (connect(sockfd, result_addr->ai_addr, (int)result_addr->ai_addrlen) == SOCKET_ERROR) {
		fprintf(stderr, "Connection failed: %d\n", WSAGetLastError());
		freeaddrinfo(result_addr);
		closesocket(sockfd);
		WSACleanup();
		return 0;
	}
	freeaddrinfo(result_addr);
	printf("Connected!\n\n");
	// Login to APRS server
	char login[128];
	sprintf(login, "user %s pass -1 vers OGN_aprs 1.0\r\n",w32nam);
	send(sockfd, login, (int)strlen(login), 0);
	// Set filter for nearby aircraft
	char filter[256];
	sprintf(filter, "#filter r/%.4f/%.4f/%.1lf\r\n", stnlat, stnlon, RNG);
	send(sockfd, filter, (int)strlen(filter), 0);
	printf("Using: %s",filter);
	// Set the socket to be non-blocking
	int mode = 1;
	if (ioctlsocket(sockfd, FIONBIO, &mode)) {
		fprintf(stderr, "Error setting non-blocking: %d\n", WSAGetLastError());
		WSACleanup();
		return 0;
	}
	linelen = 0;
	return(1);
}

// read_socket()for Windows
static int read_socket() {
	char c;
	if (sockfd < 1) { printf("sockfd=%d\n", sockfd); return(0); }
	if ((time(0)-kaltim)>300) { send(sockfd,"# keep alive",12,0); kaltim = time(0); }
	bytes_read = recv(sockfd, &c, 1, 0);
	if (bytes_read <= 0) {
		int wsaer = WSAGetLastError();
		if (bytes_read==0 || (bytes_read<0 && (wsaer==WSAEWOULDBLOCK))) {
			Sleep(100); // Sleep for 100ms to avoid busy-waiting
			return(0);
		}
		printf("recv failed ret %d errno %d\n",bytes_read,wsaer);
		getchar();
	}
	else {
		// Data received
		int crlf = c=='\r' || c=='\n';
		if (linelen>=254) { printf("line too long\n"); return(0); }
		if (linelen==0) { strcpy(line,"APRS -> "); linelen = 8; }	// new line of text
		if (linelen>8 || !crlf) {									// ignore blank lines
			line[linelen++] = c; line[linelen] = 0;
			if (crlf) linelen=0;
			return(crlf);											// true if line end
		}
	}
	return(0);
}

#else // linux
int port=50001;
struct sockaddr_in serv_addr;

static int setup_socket() {
	int flags;
	printf("Connecting to port %d\n",port);
	// Create socket
	if ((sockfd = socket(AF_INET,SOCK_STREAM,0))<0) return(0);
	// Set the socket to be non-blocking
	if ((flags = fcntl(sockfd,F_GETFL,0))==-1
	   || fcntl(sockfd,F_SETFL,flags|O_NONBLOCK)==-1) { close(sockfd); return(0); }
	serv_addr.sin_family = AF_INET;
	serv_addr.sin_port = htons(port);
	// Connect to the server (non-blocking)
	if (connect(sockfd,(struct sockaddr*)&serv_addr,sizeof(serv_addr))<0) {
		if (errno!=EINPROGRESS) { close(sockfd); return(0); }
	}
	return(1);
}
static int read_socket() {
	char c;
	if (sockfd<1) { printf("sockfd=%d\n",sockfd); return(0); }
	bytes_read = read(sockfd,&c,1);
	if (bytes_read<0) {
		if (errno==EWOULDBLOCK || errno==EAGAIN) {
			usleep(100000); // Sleep for 100ms to avoid busy-waiting
			return(0);
		}
		printf("read failed\n");
	} else if (bytes_read==0) {
		printf("Connection closed by the server\n");
	} else {
		// Data received
		line[linelen++] = c; line[linelen]=0;
		if (linelen>=255) { printf("line too long\n"); return(0); }
		if (c=='\n') {
			linelen=0;
			return(1);
		}
	}
	return(0);
}
#endif

int main(int argc,char *argv[]) {
	int aprs, cnt=0, sent, hash;
	char *s, *hasalt;
	struct val* pv;
	FILE *ff=0;
	if (argc>1) {	// use file if arg present
		use_skt=0;
	}
	setwindowsize();
	printf("\x1b[2J");	// complete clear screen
	load_config();					// configurable origin chars, a/f height, etc
	// retrieve local stn coords if possible
	FILE* fp = fopen("OGNstn.txt", "r");
	if (fp) { int r = fscanf(fp, "%lf|%lf", &stnlat, &stnlon); fclose(fp); }
	slat = (pi/180)*stnlat; slon = (pi/180)*stnlon;				// cnv to radians
	// open input stream
	if (!use_skt) {
		ff = fopen("flarm_lines2.txt","r");	// temporary source instead of socket
		if (!ff) { printf("Cannot find flarm_lines2.txt\n"); return(0); }
	} else {
		if (!setup_socket()) { printf("Setup_socket failed\n"); return(0); }
		else printf("Listening for aircraft...\n\n");
	}
	printf("Hit return"); getchar();
	setwindowsize();
	printf("\x1b[2J");	// complete clear screen
	headings();
	get_tz();
	rd_db();						// load OGNdb.txt
	signal(SIGINT,catch_sigint);	// (do not use cntl-c in Windows debugger !!)
	raw();							// non-blocking kbd (linux)
	while (!terminate) {
		pstn=0; stnrep=0; idcol=0; mtyp[0]=0, alt=0, edat=0;
		kblen = strlen(kbuf);
		if (kbhit()) keyboard();
		if ((use_skt && read_socket()) ||
			(!use_skt && fgets(line,256,ff)) && strncmp(line,"telnet>",7)) {
			if ((s=strchr(line,'\r')) || (s=strchr(line,'\n'))) strcpy(s,"$$");	// change \r\n to $$
			memcpy(cpyline,line,256);
			aprs = strncmp(line,"APRS ",5)==0;
			hash = strchr(line,'#')!=0 || strstr(line,"OGNDVS")!=0;
			hasalt = strstr(line,"/A=");
			sent = strncmp(line,"APRS <-",7)==0 || (!aprs && !hash);
			if (debug && !paused) {
				char lbuf[8];
				// mon : debug==1->only lines containing 'APRS' and no hash char or OGNDVS string
				// mone: debug==2->only lines not containing 'APRS' (extra data lines)
				// mona: debug==3->all lines
				// mons: debug==4->all lines sent only
				// monc: debug==5->all lines preceded by idle count and length in brackets.
				// monp: debug==6->all lines and set pause if origin unknown
				if ((debug==1 && aprs && !hash) || (debug==2 && !aprs) || debug==3 || (debug==4 && sent) || debug>=5) {
					if (dbgline<nxtlno) dbgline = nxtlno;
					// debug modes can be limited to lines containing exactly 6 characters typed at the prompt(typically an ident)
					strncpy(lbuf,kbuf,6); lbuf[6]=0; uc(lbuf);		// (avoid changing kbuf to upper case)
					if (kblen!=6 || strstr(line,lbuf)!=0) {			// don't list if kblen=6 and line doesn't contain lbuf
						if (debug==5) printf("\x1b[%d;1H%5d(%3d)%s\x1b[0K",dbgline,cnt,strlen(line),line);
						else printf("\x1b[%d;1H%s\x1b[0K",dbgline,line);
						if (dbgline<ipline-1) dbgline++;
						else if (nxtlno<ipline-1) dbgline = nxtlno;
						printf("\x1b[%d;1H\x1b[0K",dbgline);					// clear next line
					}
					cnt=0;
				}
				fflush(stdout);
			}
			if (aprs && !hash && hasalt && (fixlen=strchr(line+8,':')) && fixlen[1]=='/') {		// APRS report
				*fixlen=0;	fixlen+=2;								// separate varlen header
				calcBRAT(hasalt);									// set reclat,reclon,rlat,rlon,bearing,range,alt,tim
				if (gt=strchr(line+8,'>')) {
					*gt++=0;										// separate first field
					// should be one of four types of record
					if (line[5]=='<') {								// sending
						if (strstr(gt,"qOR")) locrpt();				// local report
						else if (strcmp(gt,"OGNSDR")==0) locstn();	// local station
						else disperr("tx");
					} else if (line[6]=='>') {						// receiving
						if (pstn=strstr(gt,"qAS")) remrpt();		// remote report
						else if (strstr(gt,"qAC")) {
							if (strcmp(STN,line+8)==0) locstn();	// WIN32 reported as remote
							else remstn();							// remote station
						} else disperr("rx");
					}
				} else disperr("gt");								// APRS rept without '>' or '<' in char 8 or 7
			} else if (strncmp(line+5,"sec",3)==0) locdat();		// extra data
			else { continue; }										// telnet msg ?
			// set pv for this ident's val struct
			if (!(pv=get_vptr(ident))) pv = new_val(ident,stnrep);
			// populate the val struct
			pv->hbearing = bearing;
			pv->hrange = range;
			if (stnrep) {
				// station line: ident, lat, lon, tim already set
				fixlen[25]=0;
				strcpy(pv->hlatlon,fixlen+7);
				pv->hlatlon[8]=0;
				pv->hcurcol = pv->hstarcol = defcol;
			} else {
				// flarm line: ident, rlat, rlon, alt, bearing, range, tim already set
				// try to set origin chars colour based on taxying or parked
				if (!edat && alt<APH && abs(pv->hbearing-bearing)<2 && fabs(pv->hrange-range)<0.2 && abs(pv->halt-alt)<5) {
					if (pv->hstat<4) pv->hstat++;				// static if hstat > 3
				} else if (pv->hstat>0) pv->hstat--;
				pv->halt = alt;
				strcpy(pv->hmtyp,mtyp);							// OGFLR, OGSDR, etc
				// set line colour
				if (idcol) pv->hidcol = idcol;					// ident colour if diff from line colour
				pv->hcurcol = alt<AFH ? lowcol:range>DST ? discol:actcol;
				if (pv->hstat==0 || pv->hstarcol==0) pv->hstarcol = pv->hcurcol;
				else if (pv->hstat>3) {
					pv->hstarcol = expcol;	// grey origin chars if not moving
				}
				// don't display reports which are filtered out, but keep their data updated
				if ((range>16 && bandist) || ((pv->htype=='#') && banpwr)
				|| ((strcmp(pv->hident,"300000")<0) && banpara)
				|| ((strcmp(mtyp,"OGADSB")==0) && banadsb)) pv->hlno = 0;
				if (!edat) {								// these radian values are incorrect if locdat record
					if (pv->hprevlat==0) {					// 1st recorded position
						pv->hprevlat = rlat;				// set start point
						pv->hprevlon = rlon;
					} else {
						calcBD(pv->hprevlat,pv->hprevlon);	// brng/range from last start point
						if (range>0.5) {
							pv->hrtbrng = bearing;			// route bearing
							pv->hprevlat = rlat;			// set new start point
							pv->hprevlon = rlon;
						}
					}
					pv->hlat = rlat;						// set current location
					pv->hlon = rlon;
				}
			}
			if (pstn) strcpy(pv->hstn,pstn); else pv->hstn[0]=0;
			pv->htim = tim;
			add_orichr(pv);
			displine(pv);
		}
		if (kblen==0 && timer>0 && (time(0)-timer)>=3) {
			if (redraw) {
				printf("\x1b[2J");
				headings(); pv=val;
				while (pv) {
					displine(pv);
					pv = pv->nxt;
				}
				redraw = 0;
			} else tidy_scr();								// deal with colour and order of lines
			timer = 0;
			prompt();
		}
		if (alt>200000) {
			FILE* df = fopen("OGNhigh","a+");
			if (df) { fprintf(df,"%s\n",cpyline); fclose(df); }
			else { printf("Cannot open OGNhigh\n"); exit(0); }
			if (debug==4) paused=1;
		}
		if (!banauto && scrolled>=0) {						// set/clear revscroll automatically
			if (nxtlno>=ipline) revscroll=1;
			else if (nxtlno<ipline-1) revscroll=0;
		}
	}
	if (sockfd>0) 
	#ifdef WIN32
		closesocket(sockfd);
	#else
		close(sockfd);
	#endif
	if (ff) fclose(ff);
	if (terminate==1) wr_db();	// write current db
//	ReadMode('normal');										# set STDIN back to blocking mode
	printf("\x1b[%d;1HOGNdb.txt%s written\x1b[0K\r\nOGNmon terminated\x1b[0K\r\n",botline,terminate==1 ? "" : " not");
	columns = 80; setwindowsize();
	// end - of - program
	printf("Program end\n");
	return(0);
}

// local station always on line 2
static void locstn() {
	FILE *fp;
	stnrep=1;
	ident=line+8;
	beacontim = tim;
	stnlat = reclat; stnlon = reclon;
	if (fp=fopen("OGNstn.txt","w")) { fprintf(fp,"%lf|%lf\n",stnlat,stnlon); fclose(fp); }
	slat = (pi/180)*stnlat; slon = (pi/180)*stnlon;				// cnv to radians
	tidy_scr();
}

// remote station on line 'nxtstn' (starting 3) with mvdown and inc
static void remstn() {
	stnrep=2;
	ident=pstn=line+8;
}

static void locrpt() {
	ident=line+11;
	pstn=0;
}

static void remrpt() {
	ident=line+11;
	pstn[-1]=0; strcpy(mtyp,gt);	// report type
	pstn+=4;						// reporting stn name
	if (strcmp(pstn,STN)==0) pstn=0;	// WIN32 local rpt
}

static void locdat() {
	int ht,r;
	char *s;
	double brng;
	r=sscanf(line+67,"%d",&ht); alt = (ht*3281)/1000;
	if ((s=strstr(line,"km"))==0) { printf("km abs %s\n",line); exit(0); }
	r=sscanf(s-6,"%lf",&range);
	r=sscanf(s+2,"%lf",&brng);
	bearing = (int)brng;
	line[31]=0;
	dec_tim(line+32);
	ident = line+25;
	if (line[112]=='T') idcol = notcol;			// notrack mode ident colour
	else if (line[113]=='S') idcol = stlcol;	// stealth mode ident colour
	edat = strchr(s,'?') ? 2:1;					// edat=2 if '?' near end of line, otherwise 1
}

static void makeline(struct val *pv) {
	int i, rep = pv->hstnrep;
	char *s, bbuf[8], rbuf[8], cbuf[48], *pfmt;
	memset(cbuf,0,48);
	if (pv->hrange>=99.95)	   pfmt = "%s %6d %s/%3.0lf  %s";
	else if (pv->hrange>=9.95) pfmt = "%s %6d %s/%2.1lf %s";
	else					   pfmt = "%s %6d %s/%1.1lf  %s";
	set_brng(pv->hbearing,btxt&1,bbuf);
	if (rep==0) {				// not a beacon report
		s = get_cmnt(pv->hident);			// (also ensures ident has a db entry)
		// create cmnt for ADSB and FANET
		if (strcmp(pv->hmtyp,"OGADSB")==0) strcpy(cbuf,"    ADS-B");
		else if (strcmp(pv->hmtyp,"FANET")==0) strcpy(cbuf,"    FANET");
		else strcpy(cbuf,s);										// copy comment to cbuf, and pad to 40 chars
		for (i=strlen(cbuf);i<=40;i++) cbuf[i] = i==22 ? '#':' ';	// if short cmnt, default type to pwr
		pv->htype = cbuf[22];
		sprintf(linetext,pfmt,pv->hident,pv->halt,bbuf,pv->hrange,cbuf);
	} else {					// beacon report
		sprintf(linetext,"%sStn=%-9s lat=%s, lon=%s          ",rep==1 ? "Loc":"Rem",pv->hident,pv->hlatlon,pv->hlatlon+9);
		if (rep==2) sprintf(linetext+strlen(linetext),pfmt+6,bbuf,pv->hrange,"");
		else strcat(linetext,"          ");
	}
	// add the route bearing and time
	set_brng(pv->hrtbrng,btxt&2,rbuf);
	sprintf(linetext,"%s %s(%02d%02d)",linetext,rbuf,pv->htim/60,pv->htim%60);
}

static void displine(struct val* pv) {
	char *curcol = pv->hcurcol, *idcol;
	idcol = pv->hidcol ? pv->hidcol:curcol;
	// don't display if banned or out of range
	if (pv->hlno<=0 || pv->hlno>=ipline) return;
	makeline(pv);
	printf("\x1b[%d;1H\x1b[%s%-.6s",pv->hlno,idcol,linetext);	// ident in ident colour
	printf("\x1b[%s%s",curcol,linetext+6);						// remainder in current colour
	printf("\x1b[%s %s",pv->hstarcol,pv->hstars);				// add the origin chars (previously called stars)
	printf("\x1b[0K\x1b[%s",defcol);							// erase to end of line and set default colour
	prompt();													// keep cursor at prompt
	fflush(stdout);		// bloody linux hangs up miles down the road if you don't do this
}

// fns used by spchars
static void rdrw()   { redraw=3; }
static void dtfbw()  { dump_to_file(0); }
static void dtfcol() { dump_to_file(1); }

static void dump_to_file(int m) {
	int i;
	struct val *pv;
	FILE *ff = fopen("OGNdump.txt","a");
	if (!ff) strcpy(kbuf," error");
	else {
		time_t my_time = time(NULL);
		fprintf(ff,"------------------------------------------\n");
		fprintf(ff,"%s",ctime(&my_time));
		for (i=2;i<nxtlno;i++) {
			if (pv=get_id(i)) {
				makeline(pv);
				if (m) {
					char *idcol = pv->hidcol ? pv->hidcol:pv->hcurcol;
					// ident in ident colour, rest in current colour
					fprintf(ff,"\x1b[%s%-.6s\x1b[%s%s\x1b[%s %s\n",
							idcol,linetext,pv->hcurcol,linetext+6,pv->hstarcol,pv->hstars);
				} else fprintf(ff,"%s %s\n",linetext,pv->hstars);
			} else putc('\n',ff);
		}
		if (m) fprintf(ff,"\x1b[%s",defcol);
		fclose(ff);
	}
}

static void scroll(int inc) {
	int lno;
	struct val* pv = val;
	if (revscroll) inc = inc<0 ? 1:-1;			// reverse normal scroll dirn
	if (inc<0 && nxtlno<=nxtstn) return;
	scrolled += inc;
	clearlines(nxtstn,nxtlno);
	nxtlno += inc; if (nxtlno<nxtstn) nxtlno = nxtstn;
	while (pv) {
		lno = pv->hlno;
		if (lno>=nxtstn || lno<0) {
			lno += inc;
			// dodge to allow scrolling past zero
			if (lno==-9) lno = nxtstn;
			else if (lno==nxtstn-1) lno = -10;
			pv->hlno = lno;
		}
		displine(pv);
		pv = pv->nxt;
	}
}

static void tidy_scr() {	// called every local station beacon
	int diff;
	struct val *pv = val;
	while (pv) {
		if (!pv->hstnrep) {
			diff = beacontim - pv->htim;							// mins before last local beacon
			if (diff>=MBP && !pv->hstnrep) {
				if (diff>=MBE) {									// expired timeout
					pv->hcurcol = expcol;
					if (pv->hidcol) {								// notrack or stealth expiring
						int slen = strlen(pv->hstars);
						memcpy(pv->hstars,pv->hidcol==notcol ? "NOTRACK":"STEALTH",7);
						if (slen<7) pv->hstars[7]=0;
						pv->hidcol=0;								// remove coloured id
					}
				} else pv->hcurcol = (pv->hrange<DST) ? pascol:pasdis;	// passive timeout
				pv->hstat = 4;
				pv->hstarcol = expcol;
			}
		}
		displine(pv);		// for new colours if perfsort or reorder do not change line nos.
		pv = pv->nxt;
	}
	if (sortype[0]) perfsort(); else reorder(cmpintfn,offsetof(struct val,hlno));
}

static int perfsort() {
	struct sortvars *q = get_sortvars(sortype);
	if (q) reorder(q->cmpfn,q->fldos);
	return(q!=0);
}

static int procline() {
	int n, myban = 1, job;
	char* mybuf = kbuf, *jd = " job done";
	if (mybuf[0] == '-') { mybuf++; myban = 0; }
	struct sortvars *q;
	struct filtvars *f;
	struct dbgvars  *d;
	struct spchars  *p;
	if      (job=(strcmp(kbuf,"quit")==0))				terminate=2;
	else if (job=(strcmp(kbuf,"x")==0))					sortype[0]=0;
	else if (job=(strcmp(kbuf,"16pt")==0))				m16 = 1;
	else if (job=(strcmp(kbuf,"8pt")==0))				m16 = 0;
	else if (p=get_spitem(kbuf)) { job=1; p->fn(); }	// spchars function
	if (job) { strcat(kbuf,jd); return(1); }
	else if (strstr(kbuf,jd)) { clr_kbuf(); return(1); }
	// check for known mnemonics
	// sort mnemonics cause re-order of line nos (x to clear sorting)
	if (q=get_sortvars(kbuf)) {
		strcpy(sortype,kbuf); job=1;			// new sort type
		reorder(q->cmpfn,q->fldos);
	} else if (f=get_filtvar(mybuf)) {			// filter mnemonics
			*(f->banvar) = myban; job=2;
	} else if (d=get_dbgvar(mybuf)) {			// monitor mnemonics
		if (debug=myban) {						// -mnem sets debug=0
			debug = d->val;
			dbgline = (nxtlno<ipline) ? nxtlno:ipline-1;
		} else paused=0;
		job=3;
	} else if (kbuf[6]=='=') {
		if (kcolours()) job=4;
	}
	if (job) {							// (job done)
		if (job>1) reorder(cmpintfn,offsetof(struct val,hlno));
		clr_kbuf();
	}
	if (kbuf[6]=='|') {					// db changes while running
		char *s, dbid[12], text[128];
		struct val *pv;
		if (strlen(kbuf)>56) { strcat(kbuf, " too long"); return(0); }
		strncpy(dbid,kbuf,6); dbid[6]=0;
		strcpy(text,kbuf+7);
		if (!strchr("#=:PT",text[22])) { strcat(kbuf," error"); return(0); }
		if (strlen(text)>=41) { strcat(kbuf," too long"); return(0); }
		uc(dbid);
		s = get_cmnt(dbid);				// get_cmnt creates new entry in alpha order if required
		strcpy(s,text);					// overwrite the current cmnt
		clr_kbuf();
		if (pv=get_vptr(dbid)) {		// update current line in main listing if any
			if (pv->hlno>=nxtstn) displine(pv);
		}
	}
	if (debug && (columns<200)) { columns = 215; setwindowsize(); }
	else if (!debug && (columns>200)) { columns = 125; setwindowsize(); }
	if (kbuf[0]=='#' && (n=atoi(kbuf+1))>=8) {		// '#n' sets new window size
		botline = n;
		ipline = botline-3;
		clr_kbuf();
		clearscr(); setwindowsize(); clearscr(); headings();
	}
	timer = time(0);							// reset timer
	return(job);
}

static void calcBRAT(char *hasalt) {		// set reclat, reclon, rlat, rlon, bearing, range, alt, tim
	int degns, degew, r;					// double: reclat/reclon(degrees), rlat/rlon(radians), range(km)
	char ns, ew, sl;
	if (fixlen[6]=='h') {
		r=sscanf(fixlen+7,"%2d%lf%c%c%3d%lf%c",&degns,&reclat,&ns,&sl,&degew,&reclon,&ew);
		reclat /= 60; reclon /= 60; reclat += degns; reclon += degew;
		if (ns=='S') reclat = -reclat;
		if (ew=='W') reclon = -reclon;							// record reclat/reclon in degrees
		rlat = reclat*(pi/180); rlon = reclon*(pi/180);			// record lat/lon in radians
		calcBD(slat,slon);
	} else disperr("coords");
	r=sscanf(hasalt+3,"%d",&alt);									// alt in feet (hasalt guaranteed valid)
	dec_tim(fixlen);											// time in mins
}

// calculate bearing and range from flat/flon to rlat/rlon
static void calcBD(double flat, double flon) {
	double dist = acos(sin(flat)*sin(rlat)+cos(flat)*cos(rlat)*cos(flon-rlon));
	double brng = acos((sin(rlat)-sin(flat)*cos(dist))/(sin(dist)*cos(flat)));
	if (sin(rlon-flon)<0) brng = (2*pi)-brng;
	bearing = (int)((180/pi)*brng+0.501);			// bearing in degrees
	range = (((10800*6080)/pi)*dist)/3281;			// range in km (3280.84 ft = 1km)
}

static void dec_tim(char *s) {
	int hr, mn, r;
	r=sscanf(s,"%2d%2d",&hr,&mn);
	tim = hr*60 + mn + tz;										// time in minutes
}

static char *brng_text(int brng) {
	int v=16;					// yields 3sp if brng not set (eg -ve)
	static char* points[17] = {
		"NNE"," NE","ENE","  E","ESE"," SE","SSE","  S",
		"SSW"," SW","WSW","  W","WNW"," NW","NNW","  N", "   "
	};
	if (brng>=0) {
		double d = (double)brng/11.25;
		v = (int)floor(d);
		if (v==0 || (v==1 && m16==0)) v = 32;
		// the 8 point (m16==0) formula relies on the
		// discard of the remainder of the division by 4
		v = m16 ? (v-1)/2 : (((v-2)/4)*2)+1;
	}
	return(points[v]);
}

static void set_brng(int brng,int txt,char *buf) {
	if (brng>=0) {
		if (!txt) sprintf(buf,"%03d",brng);
		else strcpy(buf,brng_text(brng));
	} else strcpy(buf,"   ");
}


static void get_tz() {
	tz = 0;
#ifndef WIN32
	// never did find how to do this in Windows
	char buf[80];
	FILE* fp = popen("date","r");
	if (fp) {
		fgets(buf,80,fp);
		tz = strstr(buf,"BST") ? 60:0;
		pclose(fp);
	}
#endif
}

static void mvdown() {			// move all flarm lines down one place
	struct val *pv = val;
	while (pv) {
		if (pv->hstnrep==0 && pv->hlno!=0) {
			pv->hlno++;
			displine(pv);
		}
		pv = pv->nxt;
	}
	nxtlno++;
}

static struct val* get_vptr(char* id) {
	// return ptr to struct with hident==id
	struct val *pv = val;
	while (pv && strcmp(pv->hident,id)) pv = pv->nxt;
	return(pv);
}

// create a new val struct on the chain
static struct val* new_val(char* id,int stnrep) {
	struct val *pv = add_val(id);
	switch (pv->hstnrep=stnrep) {
		case 0: pv->hlno = nxtlno++; break;	// next flarm line
		case 1: pv->hlno = 2;		 break;	// local station always line 2
		case 2: pv->hlno = nxtstn++;		// next remote station line
				mvdown();					// move all flarm lines down
				break;
	}
	pv->hrtbrng = -1;
	return(pv);
}

static struct val *add_val(char *id) {
	// add val struct to head of list
	struct val *pv = val;								// current first item
	val = (struct val*)memalloc(sizeof(struct val));	// new first item
	val->nxt = pv;		
	strcpy(val->hident,id);
	return(val);
}

static struct val* get_id(int lno) {
	// return ptr to struct with hlno==lno
	struct val *pv = val;
	while (pv && pv->hlno!=lno) pv = pv->nxt;
	return(pv);
}

static struct sortvars *get_sortvars(char *mnem) {
	struct sortvars *p = sortvars;
	while (p->mnem && strcmp(mnem,p->mnem)) p++;
	return(p->mnem ? p:0);
}

static struct filtvars *get_filtvar(char* mnem) {
	struct filtvars *p = filtvars;
	while (p->mnem && strcmp(mnem,p->mnem)) p++;
	return(p->mnem ? p:0);
}

static struct dbgvars *get_dbgvar(char* mnem) {
	struct dbgvars *p = dbgvars;
	while (p->mnem && strcmp(mnem,p->mnem)) p++;
	return(p->mnem ? p:0);
}

static char* get_spcmd(int c) {
	struct spchars *p = spchars;
	while (p->c && c!=p->c) p++;
	return(p->cmd);
}

static struct spchars *get_spitem(char *cmd) {
	struct spchars *p = spchars;
	while (p->c && strcmp(p->cmd,cmd)) p++;
	return(p->c ? p:0);
}

static int cmpos;		// offset in val struct for compare functions

int cmpintfn(cmparg a, cmparg b) {
	// these args are ptrs to entries in the valad array
	// struct val *p = *(struct val**)a, *q = *(struct val**)b;
	// return(p->halt - q->halt);
	// now using an offset from 'offsetof(struct val,hfield)'
	char *s = *(char**)a+cmpos, *t = *(char**)b+cmpos;
	int va = *(int*)s, vb = *(int*)t;
	return(va - vb);
}

int cmpcharfn(cmparg a, cmparg b) {
	char *s = *(char**)a+cmpos, *t = *(char**)b+cmpos;
	return(strcmp(s,t));
}

int cmpdblfn(cmparg a, cmparg b) {
	char *s = *(char**)a+cmpos, *t = *(char**)b+cmpos;
	double va = *(double*)s*100, vb = *(double*)t*100;
	return(va>=vb);
}

static void reorder(int (*cmpfn)(cmparg,cmparg), int os) {
	int n=0, j=0, size=1, wasnxt=nxtlno, waschng=0;
	struct val *pv = val;
	struct val **valad;
	// count the val structs existing (+1)
	while (pv) { size++; pv = pv->nxt; }
	// allocate space for list of val ptrs (valad)
	size *= sizeof(struct val*);
	valad = (struct val**)memalloc(size);
	// make the list of val ptrs
	pv = val;
	while (pv) {
		if (pv->hstnrep==0) valad[n++] = pv;
		pv = pv->nxt;
	}
	// sort the list of val ptrs based on chosen compare fields
	cmpos = os;										// offset in val struct used by compare functions
	qsort(valad,n,sizeof(struct val*),cmpfn);
	nxtlno = nxtstn+(scrolled>0 ? scrolled:0);
	// deal with banned lines past and present
	pv = val;
	while (pv) {
		if (!pv->hstnrep) {
			// deal with filters
			int linexp = pv->hcurcol==expcol;
			int lintax = pv->hcurcol==lowcol;
			int linpas = pv->hcurcol==pascol || pv->hcurcol==pasdis;
			int linpwr = pv->htype=='#' || pv->htype=='=';	// power type
			int lindst = pv->hrange>=DST;					// distant if 10 miles or more
			int linpara = (strcmp(pv->hident,"300000")<0) || (pv->htype=='P');
			int linadsb = strcmp(pv->hmtyp,"OGADSB")==0;
			// re - display distant, para, expired, taxying, passive, adsb, or power lines if required
			if (pv->hlno==0 && ((bandist==0 && lindst) || (banpara==0 && linpara) ||
				(banexp==0 && linexp) || (bantax==0 && lintax) ||
				(banpas==0 && linpas) || (banadsb==0 && linadsb) ||
				(banpwr==0 && linpwr))) pv->hlno = 1;		// temp line number so gets included below
			// hide distant, para, expired, taxying, passive, adsb, or power lines if required
			if (pv->hlno>0 && ((bandist && lindst) || (banpara && linpara) ||
				(banexp && linexp) || (bantax && lintax) ||
				(banpas && linpas) || (banadsb && linadsb) ||
				(banpwr && linpwr))) pv->hlno = 0;
		}
		pv = pv->nxt;
	}
	// allocate line nos in the new order of val structs
	while (j<n && (pv=valad[j++])) if (pv->hlno>0) {
		if (pv->hlno != nxtlno) waschng++;
		pv->hlno = nxtlno++;
	}
	if (waschng) {					// redisplay all if anything has changed
		clearlines(nxtstn,wasnxt);
		pv = val;
		while (pv) { displine(pv); pv = pv->nxt; }
	}
	free(valad);
	timer = time(0);
}

static void rd_db() {
	char *s, lbuf[64];
	FILE *fp = fopen("OGNdb.txt","r");
	if (!fp) { printf("Cannot open OGNdb"); return; }
	struct db **pp = &db, *pd;
	while (fgets(lbuf,64,fp)) {
		if ((s=strrchr(lbuf,'\r')) || (s=strrchr(lbuf,'\n'))) *s=0;
		if (s=strchr(lbuf,'|')) {
			*s++ = 0;
			pd = new_entry(lbuf,s);
			*pp = pd; pp = &pd->nxt;
		}
	}
	fclose(fp);
}

static void wr_db() {
	FILE *fp = fopen("OGNdb.txt","w");
	struct db *pd = db;
	if (fp) {
		while (pd) {
			if (strcmp(pd->ident,"DELETE") && strlen(pd->cmnt)>10) fprintf(fp,"%s|%s\n",pd->ident,pd->cmnt);
			pd = pd->nxt;
		}
		fclose(fp);
	} else { printf("Failed to open OGNdb.txt\n"); exit(0); }
}

static void load_config() {
	int n=0, r;
	char c, *s, *t, lbuf[128];
	FILE *fp = fopen("OGNmon.conf","r");
	if (fp) {
		memset(orichrs,0,sizeof(orichrs));
		while (fgets(lbuf,128,fp)) {
			if ((s=strchr(lbuf,'/')) || (s=strrchr(lbuf,'\r')) || (s=strrchr(lbuf,'\n'))) *s = 0;
			c = lbuf[0]; r=1;									// first char in 'c'
			// origin chars per station name
			if (c && lbuf[1]=='=') {
				if (n<MAXORI-1) {
					r=sscanf(lbuf,"%c=%s",&c,orichrs[n].stn);	// scanf removes trailing spaces
					lbuf[14]=0;
					strcpy(orichrs[n].stn,lbuf+2);
					orichrs[n++].c = c;
				} else r=0;
			} else if (c=='#') {
				// variables
				r= (sscanf(lbuf, "#define AFH %d", &AFH)	// airfield height
				 || sscanf(lbuf, "#define APH %d", &APH)	// approach height
				 || sscanf(lbuf, "#define MBP %d", &MBP)	// minutes before passive status
				 || sscanf(lbuf, "#define MBE %d", &MBE)	// minutes before expired status
				 || sscanf(lbuf, "#define DST %d", &DST));	// distant status(km)
			} else if (isalpha(c)) {
				// colours or local station variables
				if (lbuf[6]='=') {
					char *lbv = lbuf+7;
					lbuf[6]=0;
					if ((s=colbuf(lbuf)) && (t=strchr(lbv,'m'))) {
						t[1]=0; strcpy(s,lbv);
					} else {	// locstn
						if (strcmp(lbuf,"stnlat")==0)		{ stnlat = atof(lbv); slat = (pi/180)*stnlat; }
						else if (strcmp(lbuf,"stnlon")==0)	{ stnlon = atof(lbv); slon = (pi/180)*stnlon; }
						else if (strcmp(lbuf,"stnrad")==0)	RNG = atof(lbv);
						else if (strcmp(lbuf,"stnnam")==0)	strncpy(STN,lbv,9);
						else if (strcmp(lbuf,"w32nam")==0)	strncpy(w32nam,lbv,9);
						else r=0;
					}
				}
			}
			if (!r) {
				if (lbuf[6]==0) lbuf[6]='=';
				if (strlen(lbuf)>5) printf("\x1b[%d;1HCONFIG ERROR:%s\x1b[0K UNKNOWN\n",dbgline++,lbuf);
			}
		}
		fclose(fp);
	}
}

static void add_orichr(struct val *pv) {
	// get origin char for station id, or '@' if unknown
	int n=0, r=0, len = strlen(pv->hstars);
	if (len>=35) { strcpy(pv->hstars,pv->hstars+20); memset(pv->hstars+20,0,16); len=19; }
	if (pv->hstn[0]==0) r = edat ? edat>1 ? '?':'x':'#';
	else {
		while (n<MAXORI && orichrs[n].c && strcmp(orichrs[n].stn,pv->hstn)) n++;
		r = orichrs[n].c;
		if (r==0) {
			if (strncmp(pv->hstn,"PW",2)==0) r='P';
			else if (strncmp(pv->hstn,"AVX",3)==0) r='V';
			else {
				r='@';
				if (debug==6) paused=1;
			}
		}
	}
	// add char to hstars unless consecutive 'x'
	if (len==0 || r!='x' || pv->hstars[len-1]!='x') pv->hstars[len] = r;
}

static struct db *new_entry(char *id, char *cmt) {
	struct db *pd = (struct db*)memalloc(sizeof(struct db));
	strcpy(pd->ident,id); strcpy(pd->cmnt,cmt);
	return(pd);
}

static char *get_cmnt(char *id) {
	// get db entry, or add one in ident alpha order if abs
	int cmp = -1;
	struct db *pd = db, *q=0, *nxt;
	while (pd && (cmp=strcmp(id,pd->ident))>0) { q = pd; pd = pd->nxt; }
	// pd && cmp==0 - return p->cmnt.
	// pd && cmp<0  - insert id here (q was last item, p is next item)
	// q==0         - add to start of chain
	// pd==0        - add to end of chain (q was last item, next is zero)
	if (q==0 || pd==0 || cmp<0) {
		nxt = pd; pd = new_entry(id,"   ");
		pd->nxt = nxt; 
		if (q) q->nxt = pd; else db = pd;
	}
	return(pd->cmnt);
}

static struct db *exists(char *id) {		// check if ident exists in the db
	struct db *pd = db;
	while (pd && (strncmp(id,pd->ident,6))) pd = pd->nxt;
	return(pd);
}

static void prompt() {
	char* dbg = debug==1 ? "mon ":debug==2 ? "mone ":debug==3 ? "mona ":debug==4 ? "mons ":
				debug==5 ? "monc ":debug==6 ? "monp ":"";
	printf("\x1b[%d;1H\x1b[%s%s\x1b[%s %s%s%s%s%s%s%s%s%s%s\x1b[0K",ipline+1,stacol,sortype,defcol,
		bandist ? "dist ":"", bantax ? "taxy ":"", banexp ? "exp ":"",banpas ? "pas ":"", banpwr ? "pwr ":"",
		banpara ? "para ":"", banadsb ? "adsb ":"",dbg,paused ? "paused ":"",revscroll ? "scroll_rev ":""/*,
		banauto ? "banauto":""*/);	// (need another %s if banauto un-commented)
	printf("\x1b[%d;1H\x1b[%sActive, \x1b[%sTaxying, \x1b[%sDistant, \x1b[%sPassive, \x1b[%sExpired, \x1b[%sStealth, \x1b[%sNotrack\x1b[%s\x1b[0K\n\x1b[0K",
		ipline+2,actcol,lowcol,discol,pascol,expcol,stlcol,notcol,defcol);
	printf("\x1b[%d;1HSort / Filters: %s\x1b[0K",ipline,kbuf);
	fflush(stdout);	// who knew linux ?
}

static void headings() {
	printf ("\x1b[1;1HOGN Station Monitor (\x1b[%sSort\x1b[%s: ident alt brng range type time col)\
	(Filter: dist taxy exp pas pwr adsb para mon mon[asecp])\x1b[0K\n",stacol,defcol);
	if (!debug) clearscr();
	prompt();
}

static void setwindowsize() {
	printf ("\x1b[8;%d;%dt",botline+1,columns);
}

static void clearlines(int frm, int upto) {
	int i = frm, j = upto;
	if (i>j) { i=upto; j=frm; }
	printf ("\x1b[%d;1H",i);
	while (i<j && i<ipline) { printf("\x1b[0K\n"); i++; }
//printf("\x1b[%d;1H(clearlines %d to %d)   ",ipline-1,frm,upto);
}

static void clearscr() { clearlines(nxtlno,ipline); }

static void* memalloc(size_t bytes) {
	void* r = malloc(bytes);
	if (!r) { printf("malloc failure\n"); exit(0); }
	memset(r,0,bytes);
	return(r);
}

// linux doesn't have conio.h functions
#ifndef WIN32
static struct termios g_old_kbd_mode;
static void cooked(void) { tcsetattr(0, TCSANOW, &g_old_kbd_mode); }
static void raw(void) {
	static char init=0;
	struct termios new_kbd_mode;
	if (init) return;
	/* put keyboard (stdin, actually) in raw, unbuffered mode */
	tcgetattr(0, &g_old_kbd_mode);
	memcpy(&new_kbd_mode, &g_old_kbd_mode, sizeof(struct termios));
	new_kbd_mode.c_lflag &= ~(ICANON | ECHO);
	new_kbd_mode.c_cc[VTIME] = 0;
	new_kbd_mode.c_cc[VMIN] = 1;
	tcsetattr(0, TCSANOW, &new_kbd_mode);
	/* when we exit, go back to normal, "cooked" mode */
	atexit(cooked);
	init = 1;
}

static int kbhit(void) {
	struct timeval timeout;
	fd_set read_handles;
	int status;
//	raw();
	/* check stdin (fd 0) for activity */
	FD_ZERO(&read_handles);
	FD_SET(0, &read_handles);
	timeout.tv_sec = timeout.tv_usec = 0;
	status = select(1, &read_handles, NULL, NULL, &timeout);
	if (status < 0) {
		printf("\nProgram killed\n");
		exit(1);
	}
	return status;
}
static int getch(void) {
	unsigned char temp;
//	raw();
	/* stdin = fd 0 */
	if (read(0,&temp,1)!=1) return 0;
	return temp;
}
#else
	static void raw() { }	// windows conio handles this
#endif

static int uc(char *s) {
	for (int i=0;s[i];i++) s[i] = toupper(s[i]);
	return(1);
}

static int winarrow(int c) {
	int ret=0;
	if (c=='H')      ret = 'A';
	else if (c=='P') ret = 'B';
	else if (c=='M') ret = 'C';
	else if (c=='K') ret = 'D';
	return(ret);
}

static void clr_kbuf() {
	memset(kbuf,0,128); hadret=0;
	kblen=0;
}

static void keyboard() {
	int c = getch(), omitclr=0;
	char *s;
	struct db *pd;
	struct val *pv;
//	arrow keys scroll flarm lines at any time
	if ((c==0x1B && getch()=='[' && (c=getch()))
		|| (c==0xe0 && (c=winarrow(getch())))) {
		if (c=='A')		 scroll(-1);					// up arrow scroll up
		else if (c=='B') scroll(1);						// down arrow scroll down
		else if (c=='C') {								// right arrow reverse scroll dirn
			revscroll ^= 1;
			// ban automatic revscroll changes if key used to produce the opposite effect
			banauto = (nxtlno<ipline && revscroll) || (nxtlno>=ipline && !revscroll);
		} else if (c=='D') {							// left arrow
			if (kblen) { kbuf[--kblen]=0; hadret=0; }	// remove one char
		} else strcpy(kbuf,"UNK");
	} else if (kblen==0) {								// first char
		if (c=='"') btxt--;								// cycle bearing text or digits
		else if (s=get_spcmd(c)) strcpy(kbuf,s);
		else if (c==0x9c || c==0xa3 || c=='£') {		// £ displays window rows
			chk4dups(); omitclr++;						// and check for duplicate line nos
			sprintf(kbuf,"c=%x, nxtlno=%d, nxtstn=%d, scrolled=%d, \x1b[%spasdis=%s\x1b[%s ",
			    c,nxtlno,nxtstn,scrolled,pasdis,pasdis,defcol);
		} else add_to_kbuf(c);							// may be normal char
	} else if (kblen==1) {
		if (c=='=') {									// display origin name of kbuf[0]
			struct orichrs *q = orichrs;
			char *stn;
			c = kbuf[0];
			if (c=='#' || c=='x' || c=='?') stn = (pv=get_id(2)) ? pv->hident:"LocStn";
			else {
				while (q && q->c && q->c!=c) q++;
				if (q->c) {
					stn = q->stn;
				} else stn = "unknown";
			}
			sprintf(kbuf+1,"=%s",stn);
		} else add_to_kbuf(c);							// may be normal char
	} else if (kblen==6) {								// ** 7th char typed is special **
		if (c=='=') { if (kcolours()<0) strcat(kbuf," error"); }
		else if (c=='!' && debug) paused ^= 1;			// toggles monitor pause (even if key 7)
		else {
			uc(kbuf);
			pd = exists(kbuf);
			if (c=='|') {								// user typed id, and pipe in posn 7
				if (pd) { 
					cmnt = get_cmnt(kbuf);
				} else cmnt = "    new";
				sprintf(kbuf,"%s|%s",kbuf,cmnt);		// display what is known
			} else if (c=='X') {						// user typed id and X in posn 7
				if (pd) {
					strcpy(pd->ident,"DELETE");			// remove id from db
					clr_kbuf();
				}
			} else if (c=='L' || c=='N') {
				if (pd && (pv=get_vptr(pd->ident))) {
					if (c=='L') sprintf(kbuf,"%s on line %d",kbuf,pv->hlno);
					else { pv->hidcol=0; strcat(kbuf," done"); }	// remove stealth or notrack colour
				} else strcat(kbuf," unknown");
			} else if (c=='\\') clr_kbuf();
			else strcat(kbuf," error");					// not =, pipe, X, L, or N in posn 7
		}
	}
	else add_to_kbuf(c);								// perhaps normal char
	timer = time(0);									// allow time to type cmd
	if (!debug && !omitclr) clearscr();					// clear nxtlno to ipline
	prompt();
}

static void add_to_kbuf(int c) {
	if (c=='\t') {										// tab to 'type char' posn
		int i = kblen;									// (I'm really proud of the next two lines !)
		while (i<29) kbuf[i++]=' ';						// add spaces if short
		while (i>=29) kbuf[i--]=0;						// or remove chars if too long
	} 
	else if (c=='\\') clr_kbuf();						// backslash clears kbuf
	else if (c=='!' && debug) paused ^= 1;				// toggles monitor pause
	else if ((c=='\r' || c=='\n')) {					// process kbuf when return hit
		if (kblen) {									// unless empty
			hadret = 1;
			procline();
		}
	} 
	else if (c==127 || c==8) {							// del or bksp
		if (kblen) { kbuf[--kblen] = 0; hadret = 0; }	// remove one char
	} else if ((c&0x80)==0) {							// chars with 0x80 set are not required
		if (hadret) {
			clr_kbuf();
			kbuf[0]=c;									// start a different cmd
		} else if (c!=0x1B) {							// otherwise save char in kbuf (unless ESC)
			kbuf[kblen++]=c; kbuf[kblen]=0;
		}
	}
}

static char *colbuf(char* mnem) {
	struct colours *p = colours;
	while (p->mnem && strcmp(p->mnem,mnem)) p++;
	return(p->cbuf);
}

// display of colour sequence when 7th char typed is '='
// and keyboard entry of colour sequences when 7th kbuf char is '='
static int kcolours() {
	char *s, *t=0, lbuf[16];
	strncpy(lbuf,kbuf,6); lbuf[6]=0;		// lbuf holds mnemonic
	if ((s=colbuf(lbuf))==0) return(-1);	// unknown mnemonic
	if (kbuf[6]=='=') {						// process a setting line
		if (t=strchr(kbuf+7,'m')) {			// which must end with 'm'
			t[1]=0; strcpy(s,kbuf+7);
		} else strcat(kbuf," error");
	} else sprintf(kbuf,"%s=%s",lbuf,s);	// display current setting
	return(t!=0);							// true for good setting cmd
}

static void chk4dups() {
	struct val *pv = val;
	char **lident = (char**)memalloc(sizeof(char*)*100);
	dbgline = nxtlno+1;
	printf("\x1b[%d;1HChecking for duplicate line numbers",nxtlno);
	while (pv) {
		int n = pv->hlno;
		if (n>0 && lident[n]) printf("\x1b[%d;1HLine %d conflict %s %s",dbgline++,n,pv->hident,lident[n]);
		else lident[n] = pv->hident;
		pv = pv->nxt;
	}
	free(lident);
	if (dbgline==nxtlno+1)  printf("\x1b[%d;1HNone found",dbgline);
}

