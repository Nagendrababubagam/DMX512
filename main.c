// DMX512A Protocol Implementation on TM4C123GXL Launchpad
// Author: Nagendra Babu Bagam
// Email: nagendrababu.bagam@mavs.uta.edu

#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <string.h>
#include "tm4c123gh6pm.h"
#include "wait.h"

#define RED_LED      (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 1*4)))	//PF1
#define BLUE_LED     (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 2*4)))	//PF2
#define GREEN_LED    (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 3*4)))	//PF3
#define Control_PB   (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 4*4)))	//PF4
// DIP10 Switch
// 9 switches to set address of slave device in slave/device Mode
// 1 switch to denote the device as master/slave
#define DIP_1		 (*((volatile uint32_t *)(0x42000000 + (0x400053FC-0x40000000)*32 + 4*4)))	//PB4
#define DIP_2		 (*((volatile uint32_t *)(0x42000000 + (0x400043FC-0x40000000)*32 + 6*4)))	//PA6
#define DIP_3		 (*((volatile uint32_t *)(0x42000000 + (0x400043FC-0x40000000)*32 + 7*4)))	//PA7
#define DIP_4		 (*((volatile uint32_t *)(0x42000000 + (0x400243FC-0x40000000)*32 + 3*4)))	//PE3
#define DIP_5		 (*((volatile uint32_t *)(0x42000000 + (0x400243FC-0x40000000)*32 + 2*4)))	//PE2
#define DIP_6		 (*((volatile uint32_t *)(0x42000000 + (0x400243FC-0x40000000)*32 + 1*4)))	//PE1
#define DIP_7		 (*((volatile uint32_t *)(0x42000000 + (0x400073FC-0x40000000)*32 + 3*4)))	//PD3
#define DIP_8		 (*((volatile uint32_t *)(0x42000000 + (0x400073FC-0x40000000)*32 + 2*4)))	//PD2
#define DIP_9		 (*((volatile uint32_t *)(0x42000000 + (0x400073FC-0x40000000)*32 + 1*4)))	//PD1
#define DIP_10		 (*((volatile uint32_t *)(0x42000000 + (0x400073FC-0x40000000)*32 + 0*4)))	//PD0- Selected as Master/Slave select Switch
// Enable bits
#define DE_485		 (*((volatile uint32_t *)(0x42000000 + (0x400063FC-0x40000000)*32 + 6*4)))	//PC6
#define Uart1TX		 (*((volatile uint32_t *)(0x42000000 + (0x400063FC-0x40000000)*32 + 5*4)))	//PC5
#define RLED		 (*((volatile uint32_t *)(0x42000000 + (0x400053FC-0x40000000)*32 + 5*4)))	//PB5

// Global Variables
// LED Timeouts
int RedLEDTimeout=0,GreenLEDTimeout=0,BlueLEDTimeout=0;
// Device/Contoller Flag, By default Configured as device(slave)
bool _Master=false;
// Device Address, In between 0 and 511
uint16_t _DeviceAddress=0;
// States of all devices under control
uint16_t _DMXControl[513];
// Data Recieved From Controller
int _DMXRecieveData[513];
// Max Address, By default Set to 512
uint16_t _MaxAddress=512;
// Transmission ON Flag, By default set to false
bool _TxON=true;
// Poll Request Flag, By default set to false
bool _Poll=false;
// Transmission phase for transmitting data
int _TXPhase=0;
// Recieve Phase for Recieve Data
int _RXPhase=0;
// Command to work with
char _command[81]={0};
// To handle In between MAx adress change
bool maxAdd_change=false;
int val_Max=0;
uint16_t RXStartCode=0;
// local poll req.
bool poll_Req=false;
// Poll counter
int pollCounter=0;
// Poll data
int pollData[513];
// Parameters For Polling
int _Start=1,_End=512,_Mid=256;
// Orignal Max to use at Polling Time
int originalMax=512;
bool BreakReply=false, MABReply=false;
// To denote Reciever Got Poll
bool RXPoll=false;
// If Transmitter waiting for reply from Slave
bool pollReplyWait=false;
// to exit the Program
bool _ExitP=false;
//Init HardWare part
void initHw()
{
	// Configure HW to work with 16 MHz XTAL, PLL enabled, system clock of 40 MHz
    SYSCTL_RCC_R = SYSCTL_RCC_XTAL_16MHZ | SYSCTL_RCC_OSCSRC_MAIN | SYSCTL_RCC_USESYSDIV | (4 << SYSCTL_RCC_SYSDIV_S)| SYSCTL_RCC_USEPWMDIV | SYSCTL_RCC_PWMDIV_2;

    // Set GPIO ports to use APB (not needed since default configuration -- for clarity)
    // Note UART on port A must use APB
    SYSCTL_GPIOHBCTL_R = 0;

    // Enable GPIO port A and F peripherals
    SYSCTL_RCGC2_R = SYSCTL_RCGC2_GPIOA | SYSCTL_RCGC2_GPIOB | SYSCTL_RCGC2_GPIOC | SYSCTL_RCGC2_GPIOD | SYSCTL_RCGC2_GPIOE | SYSCTL_RCGC2_GPIOF;

    // Configure LED pins
    GPIO_PORTF_DIR_R = 0x0E;  // bits 1,2 and 3 are outputs, other pins are inputs
    GPIO_PORTF_DR2R_R = 0x0E; // set drive strength to 2mA (not needed since default configuration -- for clarity)
    GPIO_PORTF_DEN_R = 0x1E;  // enable LEDs
    GPIO_PORTF_PUR_R = 0x10;

    // Configure PortE(1,2,3) pins as DIP Switches(6,5,4 i/p push buttons)
    GPIO_PORTE_DIR_R = 0x00;
    GPIO_PORTE_DR2R_R=0x00;
    GPIO_PORTE_DEN_R=0x0E;
    GPIO_PORTE_PUR_R=0x0E;

    // Configure PortD(0,1,2,3) pins as DIP Switches(10,9,8,7 i/p push buttons)
    GPIO_PORTD_DIR_R=0x00;
    GPIO_PORTD_DR2R_R=0x00;
    GPIO_PORTD_DEN_R=0x0F;
    GPIO_PORTD_PUR_R=0x0F;

    // Configure PortA(6,7) pins DIP Switches(2,3 i/p push buttons)
	GPIO_PORTA_DIR_R = 0x00;
	GPIO_PORTA_DR2R_R =0x00;
	GPIO_PORTA_DEN_R = 0xC0;
	GPIO_PORTA_PUR_R = 0xC0;

	// Configure PortB(4) pin DIP Switches(1 i/p push buttons)
	GPIO_PORTB_DIR_R = 0x00;
	GPIO_PORTB_DR2R_R =0x00;
	GPIO_PORTB_DEN_R = 0x10;
	GPIO_PORTB_PUR_R = 0x10;

	// Configure PortC(6) as output pin as DE for RS485
	GPIO_PORTC_DIR_R |= 0x40;
	GPIO_PORTC_DR2R_R |=0x00;
	GPIO_PORTC_DEN_R |= 0x40;
	GPIO_PORTC_PUR_R |= 0x00;

	// Configure PortC(5) & PortC(4) as UART1 pins
	GPIO_PORTC_DIR_R |= 0x20;
	GPIO_PORTC_DR2R_R |=0x00;
	GPIO_PORTC_DEN_R |= 0x30;
	GPIO_PORTC_PUR_R |= 0x00;

	// Configure UART0 pins
    SYSCTL_RCGCUART_R |= SYSCTL_RCGCUART_R0;         // turn-on UART0, leave other uarts in same status
    __asm(" NOP");                                  // wait 3 clocks
    __asm(" NOP");
    __asm(" NOP");
    GPIO_PORTA_DEN_R |= 3;                           // default, added for clarity
    GPIO_PORTA_AFSEL_R |= 3;                         // default, added for clarity
    GPIO_PORTA_PCTL_R = GPIO_PCTL_PA1_U0TX | GPIO_PCTL_PA0_U0RX;

    // Configure UART0 to 115200 baud, 8N1 format (must be 3 clocks from clock enable and config writes)
    UART0_CTL_R = 0;                                 // turn-off UART0 to allow safe programming
    UART0_CC_R = UART_CC_CS_SYSCLK;                  // use system clock (40 MHz)
    UART0_IBRD_R = 21;                               // r = 40 MHz / (Nx115.2kHz), set floor(r)=21, where N=16
    UART0_FBRD_R = 45;                               // round(fract(r)*64)=45
    UART0_LCRH_R = UART_LCRH_WLEN_8 | UART_LCRH_FEN; // configure for 8N1 w/ 16-level FIFO
    UART0_CTL_R = UART_CTL_TXE | UART_CTL_RXE | UART_CTL_UARTEN; // enable TX, RX, and module

    // Provide clock gating for UART1
    	SYSCTL_RCGCUART_R |= SYSCTL_RCGCUART_R1;         // turn-on UART1, leave other uarts in same status
	__asm(" NOP");                                   // wait 3 clocks
	__asm(" NOP");
	__asm(" NOP");
	// Timer 1 Base Configuration
	SYSCTL_RCGCTIMER_R |= SYSCTL_RCGCTIMER_R1;      // turn-on clock for timer1
	__asm(" NOP");                                  // wait 3 clocks
	__asm(" NOP");
	__asm(" NOP");
	//Initializing Timer1 as Base timer
	// Will be configuring with corresponding time values whenever required.
	TIMER1_CTL_R &= ~TIMER_CTL_TAEN;                // turn-off timer before reconfiguring
	TIMER1_CFG_R = TIMER_CFG_16_BIT;          	 	// configure as 16-bit timer (A+B)
	TIMER1_TAMR_R = TIMER_TAMR_TAMR_1_SHOT;         // configure for 1 shot mode (count down)
	TIMER1_IMR_R = TIMER_IMR_TATOIM;                // turn-on time out interrupts
	NVIC_EN0_R |= 1 << (INT_TIMER1A-16);            // turn-on interrupt 37 (TIMER1A)

	// Timer2 Base Configuration
	SYSCTL_RCGCTIMER_R |= SYSCTL_RCGCTIMER_R2;      // turn-on clock for timer2
	__asm(" NOP");                                  // wait 3 clocks
	__asm(" NOP");
	__asm(" NOP");
	// Initializing Timer2 for poll purposes
	// Will be configuring with corresponding time values whenever required.
	TIMER2_CTL_R &= ~TIMER_CTL_TAEN;                // turn-off timer before reconfiguring
	TIMER2_CFG_R = TIMER_CFG_16_BIT;          	 	// configure as 16-bit timer (A+B)
	TIMER2_TAMR_R = TIMER_TAMR_TAMR_1_SHOT;			// configure for 1 shot mode (count down)
	TIMER2_IMR_R = TIMER_IMR_TATOIM;                // turn-on time out interrupts
	NVIC_EN0_R |= 1 << (INT_TIMER2A-16);            // turn-on interrupt 37 (TIMER1A)

	// Timer3 Base Configuration
	SYSCTL_RCGCTIMER_R |= SYSCTL_RCGCTIMER_R3;      // turn-on clock for timer3
	__asm(" NOP");                                  // wait 3 clocks
	__asm(" NOP");
	__asm(" NOP");
	// Initializing Timer3 for LED's Timeout
	TIMER3_CTL_R &= ~TIMER_CTL_TAEN;                // turn-off timer before reconfiguring
	TIMER3_CFG_R = TIMER_CFG_16_BIT;          	 	// configure as 16-bit timer (A+B)
	TIMER3_TAMR_R = TIMER_TAMR_TAMR_PERIOD;			// configure for periodic mode (count down)
	TIMER3_TAILR_R = 400000;
	TIMER3_IMR_R = TIMER_IMR_TATOIM;                // turn-on time out interrupts
	NVIC_EN1_R |= 1 << (INT_TIMER3A-16-32);            // turn-on interrupt 37 (TIMER1A)
	TIMER3_CTL_R |= TIMER_CTL_TAEN;

	// Configure LED connected to board for PWM Control(M0PWM0- PB5)
	GPIO_PORTB_DIR_R |= 0x20;   // make bit5 an output
	GPIO_PORTB_DR2R_R |= 0x20;  // set drive strength to 2mA
	GPIO_PORTB_DEN_R |= 0x20;   // enable bit5 for digital
	GPIO_PORTB_AFSEL_R |= 0x20; // select auxilary function for bit 5
	GPIO_PORTB_PCTL_R = GPIO_PCTL_PB5_M0PWM3; // enable PWM on bit 5

	// PWM Configuration
	 SYSCTL_RCGC0_R |= SYSCTL_RCGC0_PWM0;            // turn-on PWM0 module
	__asm(" NOP");                                   // wait 3 clocks
	__asm(" NOP");
	__asm(" NOP");
	SYSCTL_SRPWM_R = SYSCTL_SRPWM_R0;                // reset PWM0 module
	SYSCTL_SRPWM_R = 0;                              // leave reset state
	PWM0_1_CTL_R = 0;                                // turn-off PWM0 generator 1
	PWM0_1_GENB_R = PWM_0_GENB_ACTCMPBD_ZERO | PWM_0_GENB_ACTLOAD_ONE;
	PWM0_1_LOAD_R =1024;							 // set period to 40 MHz sys clock / 2 / 1024 = 19.5 KHz
	PWM0_INVERT_R = PWM_INVERT_PWM3INV;				 // invert outputs for duty cycle increases with increasing compare values
	PWM0_1_CMPB_R = 0;								 // Intially LED is off
	PWM0_1_CTL_R = PWM_0_CTL_ENABLE;                 // turn-on PWM0 generator 1
	PWM0_ENABLE_R = PWM_ENABLE_PWM3EN ;  		 // enable LED outputs
}

// Blocking function that writes a serial character when the UART buffer is not full
void putcUart0(char c)
{
	while (UART0_FR_R & UART_FR_TXFF);
	UART0_DR_R = c;
}

// Blocking function that writes a string when the UART buffer is not full
void putsUart0(char* str)
{
    int i;
    for (i = 0; i < strlen(str); i++)
	  putcUart0(str[i]);
}

// Blocking function that returns with serial data once the buffer is not empty
char getcUart0()
{
	while (UART0_FR_R & UART_FR_RXFE);
	return UART0_DR_R & 0xFF;
}
void Disable_UART1()
{
	UART1_CTL_R = 0;
	UART1_IM_R = 0;
	__asm(" NOP ");
	__asm(" NOP ");
	__asm(" NOP ");
}
// UART1 configuration for either reciever or Transmitter
bool Configure_UART1(char C)
{
	bool result=false;
	// Configure UART1 pins for Port C pins
	// Care need to be taken while configuring PORT C as they have Associated JTAG pins.
	GPIO_PORTC_AFSEL_R |= 0x30;                         // Selecting Alternate functions for PC4 & PC5 pins as UART pins
	GPIO_PORTC_PCTL_R |= GPIO_PCTL_PC5_U1TX | GPIO_PCTL_PC4_U1RX;
	UART1_CTL_R = 0;                                // turn-off UART1 to allow safe programming
	UART1_CC_R = UART_CC_CS_SYSCLK;                 // use system clock (40 MHz)
	UART1_IBRD_R = 10;                              // r = 40 MHz / (Nx250 kHz), set floor(r)=10, where N=16
	UART1_FBRD_R = 00;                              // round(fract(r)*64)=00
	if(C== 'T')
	{
		// Configure UART1 to 250000 baud, 8N1 format (must be 3 clocks from clock enable and config writes)
		// If the EOT  bit in UARTCTL is set, the transmit interrupt is generated if Transmission is over.
		UART1_LCRH_R = UART_LCRH_WLEN_8 | UART_LCRH_STP2; 	// configure for 8N2 w/o FIFO
		UART1_CTL_R = UART_CTL_TXE | UART_CTL_UARTEN | UART_CTL_EOT;	// enable TX, RX, EOT and module
		UART1_IM_R = UART_IM_TXIM;						//  Enable Transmission Interrupt for UART1
		NVIC_EN0_R |= 1 << (INT_UART1-16);              // turn-on interrupt 22 (UART1)
		waitMicrosecond(100);
		DE_485 = 1;
		result=true;
	}
	else if(C=='R')
	{
		// Configure UART1 to 250000 baud, 8N1 format (must be 3 clocks from clock enable and config writes)
		UART1_LCRH_R = UART_LCRH_WLEN_8 | UART_LCRH_STP2;// configure for 8N2 w/o FIFO
		UART1_CTL_R = UART_CTL_RXE | UART_CTL_UARTEN;	// enable TX, RX, EOT and module
		UART1_IM_R = UART_IM_RXIM;						//  Enable Transmission Interrupt for UART1
		NVIC_EN0_R |= 1 << (INT_UART1-16);              // turn-on interrupt 22 (UART1)
		waitMicrosecond(100);
		DE_485 = 0;
		result=true;
	}
	else
		putsUart0("Invalid UART1 configuration Option.\r\n");
	return result;
}

// To configure Timer1 with desired value
void Configure_Timer1Value(int TimeValue)
{
	TIMER1_CTL_R &= ~TIMER_CTL_TAEN;                // turn-off timer before reconfiguring
	TIMER1_TAILR_R = TimeValue;
	TIMER1_CTL_R |= TIMER_CTL_TAEN;
}
// To configure Timer1 with desired value
void Configure_Timer2Value(int TimeValue)
{
	TIMER2_CTL_R &= ~TIMER_CTL_TAEN;                // turn-off timer before reconfiguring
	TIMER2_TAILR_R = TimeValue;
	TIMER2_CTL_R |= TIMER_CTL_TAEN;
}
// 250ms Delay Routine
void wait250ms(void)
{
	__asm(" 		PUSH {R0,R1} ");
	__asm(" 		MOV R1,#250");
	__asm("Loop0:	MOV R0,#9999 "); //1ms Generation
	__asm("Loop1:	SUB R0,#1");
	__asm(" 		CBZ R0,DONE1");
	__asm(" 		B Loop1");
	__asm("DONE1:	SUB R1,#1");
	__asm(" 		CBZ R1,DONE0");
	__asm(" 		B Loop0");
	__asm("DONE0:	POP {R0,R1}" );
}
// To read Device Address
int readDeviceAddress()
{
	if(!DIP_10)
		_Master=true;
	else
		_Master=false;
	return(((!DIP_9)<<8)+((!DIP_8)<<7)+((!DIP_7)<<6)+((!DIP_6)<<5)+((!DIP_5)<<4)+((!DIP_4)<<3)+((!DIP_3)<<2)+((!DIP_2)<<1)+(!DIP_1));
}
// To get the Commnd from User
void getcommand()
{
	char c;
	int maxsize=80,count=0;
	while(1)
	{
		c=getcUart0();
		BLUE_LED=1;
		BlueLEDTimeout=10;
		if(c=='\b') //if backspace
		{
			if(count>0)
			{
				count=count-1;
			}
			else
			{
				putcUart0(' ');
			}
		}
		else if(c=='\r')
		{
			_command[count]='\0';
			break;
		}
		else
		{
			if(count==maxsize)
			{
				_command[count+1]='\0';
				break;
			}
			else
			{
				_command[count]=c;
				count=count+1;
			}
		}
	}
	return;
}
// To convert integer to string
void intTostring(int value,char *str)
{
	int num = value;
	int i=0;
	bool isNegative=false;
	char res[5];
    int len = 0;
    if(num==0)
    {
    	*str='0';
    	str++;
    	*str='\0';
    	return;
    }
    if(num<0)
    {
    	isNegative=true;
    	num=0-num;
    }
    for(; num > 0; ++len)
    {
       res[len] = num%10+'0';
       num/=10;
    }
    if(isNegative)
    {
    	res[len]='-';
    	len=len+1;
    }
    res[len] = 0; //null-terminating
    //now we need to reverse res
    for(i = 0; i < len/2; ++i)
    {
        char c = res[i]; res[i] = res[len-i-1]; res[len-i-1] = c;
    }
    for(i=0;i<len;i++)
    {
    	*str=res[i];
    	str++;
    }
    *str='\0';
}
// To extract Substring of specified length from a string
void substring(char *string, int position, int length,char *destination)
{
   memcpy(destination,string+position,length);
   destination[length]='\0';
}
// To set values of 1 for the polling from start to end
void SetPollDevices(int num)
{
	pollCounter = pollCounter+1;
	int i=1;
	for(i=1;i<=512;i++)
		pollData[i]=0;
	pollData[num]=1;
}
// To start The Transmission of data
void startTransmission()
{
	if(maxAdd_change)
	{
		_MaxAddress=val_Max;
		maxAdd_change=false;
		val_Max =0;
	}
	if(poll_Req == true)
	{
		_Poll=true;
		poll_Req=false;
		pollCounter=1;
		originalMax=_MaxAddress;
		_MaxAddress=512;
	}
	if(_Poll)
	{
		SetPollDevices(pollCounter);
	}
	if(_TxON == true && _TXPhase == 0)
	{
		// Brake signal Transmission for 92 Micro seconds
		// Disable UART1 and remove Auxilary functions from PC5 and PC4 pins for sending Break.
		Disable_UART1();
		GPIO_PORTC_PCTL_R &= ~ GPIO_PCTL_PC5_U1TX;
		GPIO_PORTC_PCTL_R &= ~ GPIO_PCTL_PC4_U1RX;
		GPIO_PORTC_AFSEL_R &= 0xCF;
		Configure_Timer1Value(3680);
		Uart1TX = 0;								// Transmit 0 for 92 Micro seconds to denote as Break
		_TXPhase = _TXPhase+1;						// Set Transmission pahse to zero(0).
	}
	else
		return;
}

// Updating The Devices Connected to Reciever
void UpdateDevices()
{
	// Update Onboard LED with Value
	PWM0_1_CMPB_R=_DMXRecieveData[_DeviceAddress];
}
// Done Polling from Transmitter side
void EndPoll()
{
	_Master = true;
	_Poll = false;
	pollCounter=0;
	_Start=1;
	_End=512;
	_Mid=255;
	_MaxAddress=originalMax;
	startTransmission();
}

// Based On Single Element search Binary Tree
void NextPollCheck(bool Result)
{
	/*if(_Start == _End)								// When reached Single Element Branch
	{
		char addr[3];
		intTostring(_Start,addr);
		putsUart0("Device Found at Adress:");
		putsUart0(addr);
		putsUart0("\r\n");
		EndPoll();
	}
	else if(Result == true)							// When slave was found then divide the band and Restart polling with left tree
	{
		_Start=_Start;
		_End = _Mid;
		_Mid = (_Start + _End)/2;
		startTransmission();
	}
	else
	{
		if(pollCounter == 1)						// Skipping first not found and redoing on 512 devices for some UART Issues.
			startTransmission();
		else if(pollCounter == 2)					// when polled 512 devices at shot and no slaves found then end poll.
		{
			EndPoll();
			putsUart0("No devices Found.\r\n");
		}
		else										// When slave wasn't found traverse polling through Right subtree.
		{
			int diff=_End - _Start;
			_Start = _End+1;
			_End = _Start+diff;
			_Mid = (_Start + _End)/2;
			startTransmission();
		}
	}*/
	if(Result == true)							// When slave was found then divide the band and Restart polling with left tree
	{
		char addr[3];
		intTostring(pollCounter,addr);
		putsUart0("Device Found at Adress:");
		putsUart0(addr);
		putsUart0("\r\n");
	}
	pollCounter = pollCounter+1;
	if(pollCounter < 513)
		SetPollDevices(pollCounter);
	else
		EndPoll();
}
// Sending Break as a reply to transmitter from reciever when device polled.
void sendBreakReply()
{
	// Brake signal Transmission for 92 Micro seconds
	// Disable UART1 and remove Auxilary functions from PC5 and PC4 pins.
	Disable_UART1();
	Configure_UART1('T');
	UART1_DR_R = 0x01;
	BreakReply = true;
}

// Timer1 ISR to serve the transmission Purpose
void Timer1Isr()
{
	TIMER1_ICR_R|=TIMER_ICR_TATOCINT;
	if(_TXPhase == 1)							// For Sending MAB signal
	{
		Configure_Timer1Value(720);
		Uart1TX = 1;							// Send 1 for 18 Microseconds for MAB.
	}
	else if(_TXPhase==2)						// For Sending Start Code
	{
		TIMER1_CTL_R &= ~TIMER_CTL_TAEN;		// Disable Timer
		Disable_UART1();
		Configure_UART1('T');					// Configure UART for Transmission.
		if(_Poll)								// Transmit poll specific Start code
			UART1_DR_R=0xF0;
		else									// Transmit Normal Data Start code
			UART1_DR_R=0x00;
	}
	_TXPhase = _TXPhase+1;						// Increment Transmission phase to Send Next Byte
}
// UART1 ISR to handle all UART1 interrupts
void Uart1Isr()
{
	if(UART1_RIS_R & UART_RIS_TXRIS)			// Transmitter Related ISR handling
	{
		RED_LED=1;
		RedLEDTimeout = 10 ;
		UART1_ICR_R |= UART_ICR_TXIC;
		if(!BreakReply)
		{
			if(_TXPhase == _MaxAddress+3)			// After Transmitting All data slots
			{
				_TXPhase=0;
				if(!_Poll)							// Re Transmit data again(Continuously.)
					startTransmission();
				else
				{									// If transmitting Poll data Make changes and Transmit data.
					_Master=false;
					//Configure_Timer2Value(3680);
					pollReplyWait = true;
					Disable_UART1();
					Configure_UART1('R');		// After Transmitting Poll data recieve the Replies.
				}
			}
			else									// While data is being Transmitted
			{
				if(!_Poll)
					UART1_DR_R=_DMXControl[_TXPhase-2];
				else
					UART1_DR_R=pollData[_TXPhase-2];
				_TXPhase=_TXPhase+1;
			}
		}
		else
		{
			Disable_UART1();
			Configure_UART1('R');
			RXPoll=false;
			BreakReply =false;
		}
	}
	else										// Reciever Related ISR Handling
	{
		GREEN_LED=1;
		GreenLEDTimeout = 10;
		UART1_ICR_R = UART_ICR_RXIC;
		__asm(" NOP ");							// Waiting Three clock cycles to read Data From DR
		__asm(" NOP ");
		__asm(" NOP ");
		uint32_t temp = UART1_DR_R;				// Read UART1 Data Register Contents
		uint32_t value = temp & 0xFF;
		if(_Poll && pollReplyWait)
		{
			TIMER2_CTL_R &= ~TIMER_CTL_TAEN;	// Disable Timeout Timer Configured.
			_Master = true;						// Change the controller back to Master
			pollReplyWait = false;				// Clear Poll reply wait flag
			if(value == 1)
			{
				NextPollCheck(true);
			}
			else
			{
				NextPollCheck(false);
			}
		}
		else
		{
			if((UART_DR_FE & temp) != 0)			// If frame Error Found
			{
				UART1_ECR_R = 0xFF;
				_RXPhase=0;
				UpdateDevices();
			}
			else										// If No frameError
			{
					if(_RXPhase<513)
					{
						if(_RXPhase == 0)
							RXStartCode = value;
						if(_RXPhase == 0 && RXStartCode == 0xf0)
							RXPoll=true;
						_DMXRecieveData[_RXPhase]=value;
						_RXPhase=_RXPhase+1;
						if(RXPoll && (_RXPhase == 513))	// Wait till recieve all the data and reply
						{
							if(_DMXRecieveData[_DeviceAddress] == 1)
								sendBreakReply();
						}
					}
			}
		}
	}
}
// Timer2 for Processing poll timeouts
void Timer2Isr()
{
	TIMER2_ICR_R |= TIMER_ICR_TATOCINT;
	if(DIP_10)										// When slave is Giving Break signal as Reply
	{
		if(BreakReply)
		{
			Disable_UART1();
			Configure_UART1('R');
			RXPoll=false;
			BreakReply =false;
		}
	}
	else if(pollReplyWait == true)					// When Master is waiting for Reply
	{
		// waiting for the reply from reciever
		// If you don't recieve any reply from reciever
		TIMER2_CTL_R &= ~TIMER_CTL_TAEN;
		_Master = true;
		pollReplyWait = false;
		//DE_485=1;
		NextPollCheck(false);
	}
}
// Timer3 ISR which controls LED's and fires @ every 10ms
void Timer3Isr()
{
	TIMER3_ICR_R |= TIMER_ICR_TATOCINT;
	if(RedLEDTimeout >0)
		RedLEDTimeout =RedLEDTimeout -1;
	else
		RED_LED = 0;
	if(GreenLEDTimeout >0)
		GreenLEDTimeout =GreenLEDTimeout -1;
	else
		GREEN_LED = 0;
	if(BlueLEDTimeout >0)
		BlueLEDTimeout =BlueLEDTimeout -1;
	else
		BLUE_LED = 0;
}
// Tried polling using Frame error
/*void ConfigForReply()
{
	DE_485=0;
	UART1_CTL_R = 0;                                // turn-off UART1 to allow safe programming
	UART1_CC_R = UART_CC_CS_SYSCLK;                 // use system clock (40 MHz)
	UART1_IBRD_R = 10;                              // r = 40 MHz / (Nx250 kHz), set floor(r)=10, where N=16
	UART1_FBRD_R = 00;                              // round(fract(r)*64)=00
	UART1_LCRH_R = UART_LCRH_WLEN_8 | UART_LCRH_STP2; 	// configure for 8N2 w/o FIFO
	UART1_CTL_R = UART_CTL_RXE | UART_CTL_UARTEN;	// enable TX, RX, EOT and module
	UART1_IM_R = UART_IM_FEIM;						//  Enable Transmission Interrupt for UART1
	NVIC_EN0_R |= 1 << (INT_UART1-16);              // turn-on interrupt 22 (UART1)
}*/

// processes the command and returns argument count and updates command,fieldPos and fieldType arrays
bool CommandTokenization_Processing()
{
	int m_argCount=0;
	char m_LocalCommandCopy[81]={0};
	int m_fieldPos[5]={0};
	char m_fieldType[5];
	int m_errorPos[10]={0};
	int m_fieldPointer=0;
	int m_errPointer=0;
	char m_prev='d'; //d- for delimiter, a- for alphabets,n- for numericals
	int i=0;
	memcpy(m_LocalCommandCopy,_command,strlen(_command));
	while(_command[i] != '\0')
	{
		if((_command[i]>=65 && _command[i]<=90)||(_command[i]>=97 && _command[i]<=122))
		{
			_command[i]=tolower(_command[i]);
			if(m_prev=='d')
			{
				m_fieldPos[m_fieldPointer]=i;
				m_fieldType[m_fieldPointer]='a';
				m_fieldPointer=m_fieldPointer+1;
			}
			else if (m_prev == 'n')
			{
				m_errorPos[m_errPointer]=i;
				m_errPointer=m_errPointer+1;
				break;
			}
			m_prev = 'c';
		}
		else if(_command[i]>=48 && _command[i]<=57)
		{
			if(m_fieldPointer==0)
			{
				m_errorPos[m_errPointer]=i;
				m_errPointer=m_errPointer+1;
				break;
			}
			if(m_prev=='d')
			{
				m_fieldPos[m_fieldPointer]=i;
				m_fieldType[m_fieldPointer]='n';
				m_fieldPointer=m_fieldPointer+1;
			}
			else if (m_prev=='c')
			{
				m_errorPos[m_errPointer]=i;
				m_errPointer=m_errPointer+1;
				break;
			}
			m_prev='n';
		}
		else
		{
			m_prev='d';
			_command[i]= '\0';
		}
		i=i+1;
	}
	m_argCount=m_fieldPointer;
	// Handle Error Pointer Before Proceeding
	// If m_errPointer > 0 i.e error in command
	if(m_errPointer>0)
	{
		i=0;
		int errP=m_errorPos[0]+2; // 2 added as I have command promt >>
		while(i!=errP)
		{
			putcUart0(' ');
			i++;
		}
		putcUart0('^');
		putsUart0("\r\n");
		return false;
	}
	// Arg count>3 Its error as of now as we haven't designed any command with 4 Arguments
	if(m_argCount == 0 || m_argCount > 3 || m_fieldType[0] == 'n')
	{
		putsUart0("Command Entered is Invalid.\r\n");
		return false;
	}
	// If first part of command is numeric,Its invalid
	// Command Processing
	char m_inst[80]={'\0'};
	char m_address[80]={'\0'};
	char m_value[80]={'\0'};
	int j=0;
	int m_length=0;
	switch(m_argCount)
	{
	case 3:
		j=0,m_length=0;
		for(j=m_fieldPos[2];_command[j]!='\0';j++)
				m_length=m_length+1;
		substring(_command,m_fieldPos[2],m_length,m_value);
	case 2:
		j=0,m_length=0;
		for(j=m_fieldPos[1];_command[j]!='\0';j++)
				m_length=m_length+1;
		substring(_command,m_fieldPos[1],m_length,m_address);
	case 1:
		j=0,m_length=0;
		for(j=m_fieldPos[0];_command[j]!='\0';j++)
				m_length=m_length+1;
		substring(_command,m_fieldPos[0],m_length,m_inst);
		break;
	default:
		return false;
	}
	int m_CAddress=-1;
	int m_CValue=-1;
	if(m_address[0]!= '\0')
	{
		m_CAddress = atoi(m_address);
		if(!(strcmp(m_inst,"max")==0)&&(m_CAddress > _MaxAddress || m_CAddress == -1 || m_CAddress == 0))
		{
			char l_mem[4];
			memset(l_mem,0,strlen(l_mem));
			intTostring(_MaxAddress,l_mem);
			putsUart0("Address you Entered in the Command is Invalid.\r\n");
			putsUart0("Valid Adresses are 1 to ");
			putsUart0(l_mem);
			putsUart0("\r\n");
			return false;
		}
	}
	if(m_value[0]!= '\0')
	{
		m_CValue = atoi(m_value);
		if(m_CValue > 255 || m_CValue == -1 )
		{
			putsUart0("Value you Entered in the Command is Invalid.\r\n");
			putsUart0("valid Values are 1 to 255.\r\n");
			return false;
		}
	}
	// SET Command
	if(strcmp(m_inst,"set")==0)
	{
		if(m_argCount>3)
			return false;
		if(m_CAddress==-1 || m_CValue ==-1)
		{
			putsUart0("Address & Value fields for set are not provided.\r\n");
			return false;
		}
		_DMXControl[m_CAddress]=m_CValue;
	}
	else if(strcmp(m_inst,"clear")==0)
	{
		if(m_argCount>1)
			return false;
		//Clear DMX Array
		int i=1;
		for(i=1;i<513;i++)
			_DMXControl[i]=0;
	}
	else if(strcmp(m_inst,"get")==0)
	{
		if(m_argCount>2)
			return false;
		if(m_CAddress==-1)
		{
			putsUart0("Address for get is not provided.\r\n");
			return false;
		}
		uint16_t aInt=0;
		char str[4];
		memset(str,0,strlen(str));
		aInt=_DMXControl[m_CAddress];
		if(aInt==0)
		{
			str[0]=48;
			str[1]='\0';
		}
		else
			intTostring(aInt,str);
		putsUart0("Value at Address you Entered in Command is: ");
		putsUart0(str);
		putsUart0("\r\n");
	}
	else if(strcmp(m_inst,"max")==0)
	{
		if(m_argCount>2)
			return false;
		if(m_CAddress==-1)
		{
			putsUart0("Address to set for max is not provided.\r\n");
			return false;
		}
		if(_TxON && _Master) // If transmission is Ongoing
		{
			maxAdd_change=true;
			val_Max=m_CAddress;
		}
		else
		{
			_MaxAddress=m_CAddress;
		}
	}
	else if(strcmp(m_inst,"on")==0)
	{
		if(m_argCount>1)
			return false;
		if(_TxON==true)
		{
			putsUart0("Transmission is Already On\r\n");
		}
		else
		{
			_TxON=true;
			startTransmission();
		}
	}
	else if(strcmp(m_inst,"off")==0)
	{
		if(m_argCount>1)
			return false;
		if(_TxON==false)
			putsUart0("Transmission is Already off\r\n");
		else
			_TxON=false;
	}
	else if(strcmp(m_inst,"poll")==0)
	{
		if(m_argCount>1)
			return false;
		if(!(_TxON==true && _Master==true))
		{
			putsUart0("Poll Can not be done as DataTransmission is Not on.\r\n");
		}
		else
		{
			poll_Req=true;
			putsUart0("Poll Command Accepted\r\n");
		}
	}
	else if(strcmp(m_inst,"exit")==0)
	{
		if(m_argCount>1)
			return false;
		_ExitP = true;
	}
	else if(strcmp(m_inst,"help")==0)
	{
		putsUart0("Possible Commands are: \r\n");
		putsUart0("\t'set A, V'\t-\tThe controller should update the value being transmitted to DMX address A to a value of V.\r\n");
		putsUart0("\t'get A'\t-\tThe controller should return the value being sent to DMX address A.\r\n");
		putsUart0("\t'clear'\t-\tThe values of all 512 DMX addresses sent on the primary data link shall be set to zero.\r\n");
		putsUart0("\t'on'\t-\tThe DMX stream shall be sent continuously.\r\n");
		putsUart0("\t'off'\t-\tThe DMX stream will not be sent.\r\n");
		putsUart0("\t'max M'\t-\tThe maximum address transmitted shall be M. The default value is 512.\r\n");
		putsUart0("\t'poll'\t-\tA series of experimental poll requests are sent to find what devices are on the bus.\r\n");
		putsUart0("\t'exit'\t-\tTo Exit the Program.\r\n");
		putsUart0("\t'Help'\t-\tTo get help on possible commands\r\n");
	}
	else
	{
		putsUart0("Command Entered is Invalid. \r\n");
		return true;
	}
	putsUart0("Command Processed Successfully --> ");
	putsUart0(m_LocalCommandCopy);
	putsUart0("\r\n");
	return true;
}

/*
 * main.c
 */
int main(void)
{
	uint16_t m_deviceAddress;
	char m_add[4];
	bool m_success=false;
	initHw();
	putsUart0("\r\n DMX512 Prototype \r\n");
	// Turning on Status LED for 250ms on powerup
	BLUE_LED =1;
	BlueLEDTimeout = 25;
	// Read Device Address
	m_deviceAddress=readDeviceAddress();
	memset(m_add,0,strlen(m_add));
	intTostring(m_deviceAddress,m_add);
	//Assigning Address selected to global deviceadress variable
	_DeviceAddress=m_deviceAddress;
	if(_Master)
		putsUart0("Device Configured as Master\\Controller \r\n");
	else
		putsUart0("Device Configured as Slave\r\n");
	putsUart0("Device Current Address : ");
	intTostring(_DeviceAddress,m_add);
	putsUart0(m_add);
	putsUart0("\r\n");
	if(_Master == true)
	{
		startTransmission();
		putsUart0("Please enter your Commands:\r\n");
		while(!_ExitP)
		{
			while(_Poll | poll_Req ); 	// Wait untill polling is over if it is ongoing
			memset(_command,'\0', 81);  // Clearing Command Array to accept new Command
			putsUart0("Ready! \r\n");
			putsUart0(">>");
			getcommand();
			putsUart0("\r\n");
			m_success=CommandTokenization_Processing();
			if(!m_success)
			{
				putsUart0("FAIL.Invalid Command.\r\nType help for Help on Commands\r\n");
				continue;
			}
		}
	}
	else
	{
		putsUart0("Recieving Data.....\r\n");
		Configure_UART1('R');
		while(1);
	}
	_TxON=false;
	putsUart0("Thank you! \r\n");
	return 0;
}



