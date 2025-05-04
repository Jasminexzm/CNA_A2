#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "sr.h"
#include <string.h>

/* ******************************************************************
   Go Back N protocol.  Adapted from J.F.Kurose
   ALTERNATING BIT AND GO-BACK-N NETWORK EMULATOR: VERSION 1.2  

   Network properties:
   - one way network delay averages five time units (longer if there
   are other messages in the channel for GBN), but can be larger
   - packets can be corrupted (either the header or the data portion)
   or lost, according to user-defined probabilities
   - packets will be delivered in the order in which they were sent
   (although some can be lost).

   Modifications: 
   - removed bidirectional GBN code and other code not used by prac. 
   - fixed C style to adhere to current programming style
   - added GBN implementation
**********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet */
#define SEQSPACE 7      /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver  
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your 
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ ) 
    checksum += (int)(packet.payload[i]);

  return checksum;
}

int IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return -1;
  else
    return 0;
}


/********* Sender (A) variables and functions ************/

static struct pkt buffer[WINDOWSIZE];  /* array for storing packets waiting for ACK */
static int windowfirst, windowlast;    /* array indexes of the first/last packet awaiting ACK */
static int windowcount;                /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;
  int buf_index;
  int seqfirst = windowfirst;
  int seqlast = (windowfirst + WINDOWSIZE - 1) % SEQSPACE;

  /* if not blocked waiting on ACK */
  if (((seqfirst <= seqlast) && (A_nextseqnum >= seqfirst && A_nextseqnum <= seqlast)) ||
      ((seqfirst > seqlast) && (A_nextseqnum >= seqfirst || A_nextseqnum <= seqlast)))
  {
    if (TRACE > 1)
      printf("----A: New message arrives, window is not full, send new packet to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for (i = 0; i < 20; i++)
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* compute buffer index */
    if (A_nextseqnum >= windowfirst)
      buf_index = A_nextseqnum - seqfirst;
    else
      buf_index = WINDOWSIZE - seqfirst + A_nextseqnum;

    /* put packet in window buffer */
    buffer[buf_index] = sendpkt;
    windowcount++;

    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3(A, sendpkt);

    /* start timer if this is the first unACKed packet in the window */
    if (windowcount == 1)
      starttimer(A, RTT);

    /* update next sequence number */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;
  }
  else
  {
    /* window is full */
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}

/* called from layer 3, when a packet arrives for layer 4 
   In this practical this will always be an ACK as B never sends data.

  This function handles the ACKs received from receiver B.
  Unlike Go-Back-N, where a cumulative ACK causes the sender to slide its window all at once,
  Selective Repeat treats each ACK independently. Therefore:
  
  1. We first check whether the ACK is corrupted.
  2. Then we verify if the ACK falls within the current sender window.
     Since sequence numbers wrap around in SR, we need to account for circular indexing.
  3. If the ACK is valid and hasn't been seen before:
     - We mark the corresponding packet as acknowledged in the buffer.
     - If it ACKs the base of the window (windowfirst), we try to advance the window.
       This is done by checking how many consecutive ACKs (starting from base) we’ve received.
       We then shift the buffer, update the window start pointer, and restart the timer.
  4. If the ACK is a duplicate (already marked), we simply ignore it.
  5. If the ACK is not for the base but within the window, we still mark it as acknowledged.
     It may help slide the window later when earlier packets get ACKed.
*/

void A_input(struct pkt packet)
{
  int i;
  int index;
  int seqfirst = windowfirst;
  int seqlast = (windowfirst + WINDOWSIZE - 1) % SEQSPACE;

  /* Check if ACK is not corrupted */
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n", packet.acknum);
    total_ACKs_received++;

    /* Check if ACK is within the current sender window */
    if (((seqfirst <= seqlast) && (packet.acknum >= seqfirst && packet.acknum <= seqlast)) ||
        ((seqfirst > seqlast) && (packet.acknum >= seqfirst || packet.acknum <= seqlast))) {

      /* Calculate index of this ACK in the buffer */
      if (packet.acknum >= seqfirst)
        index = packet.acknum - seqfirst;
      else
        index = WINDOWSIZE - (seqfirst - packet.acknum);

      /* If this ACK has not been received before */
      if (buffer[index].acknum == NOTINUSE) {
        if (TRACE > 0)
          printf("----A: ACK %d is not a duplicate\n", packet.acknum);
        buffer[index].acknum = packet.acknum;
        windowcount--;
        new_ACKs++;
      } else {
        /* Duplicate ACK, ignore */
        if (TRACE > 0)
          printf("----A: duplicate ACK %d received, do nothing!\n", packet.acknum);
      }

      /* Try to slide the window forward if possible */
      int slide = 0;
      for (i = 0; i < WINDOWSIZE; i++) {
        if (buffer[i].acknum != NOTINUSE)
          slide++;
        else
          break;
      }

      if (slide > 0) {
        /* Update the window start pointer */
        windowfirst = (windowfirst + slide) % SEQSPACE;

        /* Shift buffer left by 'slide' positions */
        for (i = 0; i < WINDOWSIZE - slide; i++) {
          buffer[i] = buffer[i + slide];
        }

        /* Clear remaining buffer entries */
        for (i = WINDOWSIZE - slide; i < WINDOWSIZE; i++) {
          buffer[i].acknum = NOTINUSE;
          memset(buffer[i].payload, 0, sizeof(buffer[i].payload));
        }

        /* Stop and restart timer if necessary */
        stoptimer(A);
        if (windowcount > 0)
          starttimer(A, RTT);
      }
    }
  } else {
    /* Corrupted ACK received, ignore */
    if (TRACE > 0)
      printf("----A: corrupted ACK is received, do nothing!\n");
  }
}

/* called when A's timer goes off */
/* When it is necessary to resend a packet, the oldest unacknowledged packet should be resent*/
void A_timerinterrupt(void)
{
  /* Timeout occurred, resend the earliest unACKed packet */
  if (TRACE > 0)
    printf("----A: timeout occurred, resending base packet\n");

  if (windowcount > 0) {
    tolayer3(A, buffer[0]);  /* resend the packet at the base of the window */
    if (TRACE > 0)
      printf("----A: resending packet %d\n", buffer[0].seqnum);
    packets_resent++;

    /* Restart the timer */
    starttimer(A, RTT);
  }
}

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;   /* windowlast is where the last packet sent is stored.  
		     new packets are placed in winlast + 1 
		     so initially this is set to -1
		   */
  windowcount = 0;
}



/********* Receiver (B)  variables and procedures ************/

static int expectedseqnum; /* the sequence number expected next by the receiver */
static int B_nextseqnum;   /* the sequence number for the next packets sent by B */
static struct pkt buffer_b[WINDOWSIZE];
static int windowfirst;
static int receivelast;


/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;
  int pckcount = 0;
  int seqfirst;
  int seqlast;
  int index;

  /* if not corrupted and received packet is in order */
  if  ( (!IsCorrupted(packet))  && (packet.seqnum == expectedseqnum) ) 
  {
    if (TRACE > 0)
      printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
    packets_received++;

    /* deliver to receiving application */
    tolayer5(B, packet.payload);

    /*create sendpkt*/

    /* send an ACK for the received packet */
    sendpkt.acknum = expectedseqnum;
    sendpkt.seqnum = NOTINUSE;

    /*we don't have any data to send, and fill payload with 0's */
    for (i = 0; i < 20; i++)
      sendpkt.payload[i] = '0';
    
    /* computer checksum */
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* send out packet */
    tolayer3 (B, sendpkt);

    /* check if new packet or duplicate */
    seqfirst = windowfirst;
    seqlast = (windowfirst + WINDOWSIZE -1) % SEQSPACE;

    /* see if the packet recevied is inside the window */
    if (((seqfirst <= seqlast) && (packet.seqnum >= seqfirst && packet.seqnum <= seqlast))||
        ((seqfirst > seqlast) && (packet.seqnum >= seqfirst || packet.seqnum <= seqlast)))

    {
      /* get index */
      if (packet.seqnum >= seqfirst)
        index = packet.seqnum - seqfirst;
      
      else 
        index = WINDOWSIZE - seqfirst + packet.seqnum;

      /* keep receivelast */
      receivelast = receivelast > index ? receivelast:index;

      /* if not duplicate, save to buffer */
      if (strcmp(buffer_b[index].payload, packet.payload) != 0)
      {
        /* buffer it */
        packet.acknum = packet.seqnum;
        buffer_b[index] = packet;

        /* if it is the base */
        if (packet.seqnum == seqfirst){
          for (i = 0; i < WINDOWSIZE; i++)
          {
            if (buffer_b[i].acknum >= 0 && strcmp(buffer_b[i].payload, "") != 0)
              pckcount++;
            else
              break;
          }

          /* update state variables */
          windowfirst = (windowfirst +pckcount) % SEQSPACE;

          /* update buffer*/
          for (i = 0; i < WINDOWSIZE; i++)
          {
            if ((i + pckcount) <= (receivelast + 1))
              buffer_b[i] = buffer_b[i + pckcount];
          }
        }
        /* deliver to receving application*/
        tolayer5(B,packet.payload);
      }
    }   
  }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  expectedseqnum = 0;
  B_nextseqnum = 1;
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)  
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}

