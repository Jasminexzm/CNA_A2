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
static int acked[WINDOWSIZE];  /* 0 = false, 1 = true */

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
    int index,slide = 0;
    int i;
    int seqfirst, seqlast;
    int ackcount;

    /* Check if ACK is not corrupted */
    if (!IsCorrupted(packet)) {
        if (TRACE > 0)
            printf("----A: uncorrupted ACK %d is received\n", packet.acknum);
        total_ACKs_received++;

        seqfirst = windowfirst;
        seqlast = (windowfirst + WINDOWSIZE - 1) % SEQSPACE;
        ackcount = 0;

        /* Check if ACK is within the current window */ 
        if (((seqfirst <= seqlast) && (packet.acknum >= seqfirst && packet.acknum <= seqlast)) ||
            ((seqfirst > seqlast) && (packet.acknum >= seqfirst || packet.acknum <= seqlast))) {

            /* Compute buffer index for the acked packet */
            if (packet.acknum >= seqfirst)
                index = packet.acknum - seqfirst;
            else
                index = WINDOWSIZE - (seqfirst - packet.acknum);

            /* If not already acknowledged */
            if (!acked[index]) {
                acked[index] = true;
                windowcount--;
                new_ACKs++;
            }

            /*Slide the window if possible*/ 
            for (i = 0; i < WINDOWSIZE; i++) {
                if (acked[i])
                    slide++;
                else
                    break;
            }

            if (slide > 0) {
                windowfirst = (windowfirst + slide) % SEQSPACE;

                /* Shift buffer and acked flags */
                for (i = 0; i < WINDOWSIZE - slide; i++) {
                    buffer[i] = buffer[i + slide];
                    acked[i] = acked[i + slide];
                }

                for (i = WINDOWSIZE - slide; i < WINDOWSIZE; i++) {
                    acked[i] = false;
                    buffer[i].acknum = NOTINUSE;
                    memset(buffer[i].payload, 0, sizeof(buffer[i].payload));
                }

                /* Restart timer if there are still unacknowledged packets */
                stoptimer(A);
                if (windowcount > 0)
                    starttimer(A, RTT);
            }
        }
    } else {
        if (TRACE > 0)
            printf("----A: corrupted ACK received, ignored\n");
    }
}

/* called when A's timer goes off */
/* When it is necessary to resend a packet, the oldest unacknowledged packet should be resent*/
void A_timerinterrupt(void)
{
    /* Timeout occurred: resend the oldest unacknowledged packet */
    if (TRACE > 0)
        printf("----A: timeout occurred, resending oldest unACKed packet\n");

    if (windowcount > 0) {
        tolayer3(A, buffer[0]);
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
  int i;

    A_nextseqnum = 0;
    windowfirst = 0;
    windowlast = -1;
    windowcount = 0;

    /* Initialize the ack tracking array */
    for (i = 0; i < WINDOWSIZE; i++) {
        acked[i] = false;
        buffer[i].acknum = NOTINUSE;
        memset(buffer[i].payload, 0, sizeof(buffer[i].payload));
    }
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
    struct pkt ackpkt;

    if (!IsCorrupted(packet)) {
        if (TRACE > 0)
            printf("----B: received packet %d\n", packet.seqnum);
        packets_received++;

        /* If expected sequence number, deliver and send ACK */
        if (packet.seqnum == expectedseqnum) {
            tolayer5(B, packet.payload);

            /* Prepare ACK */
            ackpkt.seqnum = NOTINUSE;
            ackpkt.acknum = expectedseqnum;
            memset(ackpkt.payload, 0, sizeof(ackpkt.payload));
            ackpkt.checksum = ComputeChecksum(ackpkt);
            tolayer3(B, ackpkt);

            /* Move expected sequence number forward */
            expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
        }
        else {
            /* Out-of-order packet: still ACK to support SR */
            ackpkt.seqnum = NOTINUSE;
            ackpkt.acknum = packet.seqnum;
            memset(ackpkt.payload, 0, sizeof(ackpkt.payload));
            ackpkt.checksum = ComputeChecksum(ackpkt);
            tolayer3(B, ackpkt);

            if (TRACE > 0)
                printf("----B: out-of-order packet %d received, buffered/ignored\n", packet.seqnum);
        }
    } else {
        if (TRACE > 0)
            printf("----B: corrupted packet received, ignored\n");
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

