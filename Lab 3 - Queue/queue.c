  /*
 * Developed by R. E. Bryant, 2017
 * Extended to store strings, 2018
 */

/*
 * This program implements a queue supporting both FIFO and LIFO
 * operations.
 *
 * It uses a singly-linked list to represent the set of queue elements
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "harness.h"
#include "queue.h"

/*
  Create empty queue.
  Return NULL if could not allocate space.
*/
queue_t *q_new()
{
    queue_t *q =  malloc(sizeof(queue_t));
    if(q == NULL) {
      return NULL; //if malloc returned NULL then return NULL
    }

    q->head = NULL;  //sets head and tail to null, and sets initial size to 0
    q->tail = NULL;
    q->size = 0;

    return q;
}

/* Free all storage used by queue */
void q_free(queue_t *q)
{
    if(q == NULL){  //if the current queue is null, return
      return;
    }

    list_ele_t *curr = q->head;  //set curr equal to q's head
    list_ele_t *currToFree = NULL;  //initialize currToFree to NUll - will be used ad a temp

    while(curr != NULL) {
      currToFree = curr; //set temp list element fo be freed

      curr = curr->next; //go to next list element in the queue

      free(currToFree->value); //free the string
      free(currToFree);  //free the list element
    }

    /* Free queue structure */
    free(q);
}

/*
  Attempt to insert element at head of queue.
  Return true if successful.
  Return false if q is NULL or could not allocate space.
  Argument s points to the string to be stored.
  The function must explicitly allocate space and copy the string into it.
 */
bool q_insert_head(queue_t *q, char *s)
{
  /* Don't forget to allocate space for the string and copy it */
  /* What if either call to malloc returns NULL? */

    if(q == NULL){ //if current queue is null, return false
      return false;
    }

    list_ele_t *newh = malloc(sizeof(list_ele_t));  //allocate space for the new list element

    if(newh == NULL){ //if call to malloc returned NULL, then return false
      return false;
    }

    newh->value = malloc(strlen(s) + 1);            //allocate space for the new list element's value

    if(newh->value == NULL) { //if call to malloc returned NULL, then return false
      free(newh);              //also you need to free the space allocated for the list element
      return false;
    }

    strcpy(newh->value, s); //copy s into the new list element's value

    newh->next = q->head;  //set the new list element's next value to the head of current queue so list element is now at front
    q->head = newh;       //set head of queue to new list element

    if(q->size == 0) {
      q->tail = newh; //if this is the first element, then it is the head and tail
    }

    q->size += 1;    //increment the queue's size counter

    return true;
}


/*
  Attempt to insert element at tail of queue.
  Return true if successful.
  Return false if q is NULL or could not allocate space.
  Argument s points to the string to be stored.
  The function must explicitly allocate space and copy the string into it.
 */
bool q_insert_tail(queue_t *q, char *s)
{
    /* You need to write the complete code for this function */
    /* Remember: It should operate in O(1) time */

    if(q == NULL){ //if current queue is null, return false
      return false;
    }

    list_ele_t *newtail = malloc(sizeof(list_ele_t));  //allocate space for the new list element

    if(newtail == NULL){ //if call to malloc returned NULL, then return false
      return false;
    }

    newtail->value = malloc(strlen(s) + 1);            //allocate space for the new list element's value

    if(newtail->value == NULL) { //if call to malloc returned NULL, then return false
      free(newtail);             //also you need to free the space allocated for the list element
      return false;
    }

    strcpy(newtail->value, s); //copy s into the new list element's value
    newtail->next = NULL; //set the new tail element's next to null

    if(q->size == 0) { //if the queue is empty
      q->head = newtail;  //set the new list element to the head and the tail
      q->tail = newtail;
      q->size += 1;   //increment the queue's size
      return true;
    }

    if(q->size > 0) {
      q->tail->next = newtail; //set the queue's current tail's next field to the new tail
      q->tail = newtail;  //set the new list element to the tail
      q->size += 1;    //increment the queue's size
      return true;
    }

    return false;
}

/*
  Attempt to remove element from head of queue.
  Return true if successful.
  Return false if queue is NULL or empty.
  If sp is non-NULL and an element is removed, copy the removed string to *sp
  (up to a maximum of bufsize-1 characters, plus a null terminator.)
  The space used by the list element and the string should be freed.
*/
bool q_remove_head(queue_t *q, char *sp, size_t bufsize)
{
    if(q == NULL || q->size == 0 || sp == NULL) { //if current queue is null, return false   OR if the current queue is empty, then there is no head to remove
      return false;
    }

    char *removedString = q->head->value;  //removed string

    while(bufsize - 1 > 0) { //up to a maximum of bufsize-1 characters
      *sp = *removedString;  //copying the removed string to sp - this starts at the first character in the removed string

      sp += 1;               //moves sp to the next character in the string
      removedString += 1;    //moves removedString to the next character in the string

      bufsize -=1;  //decrement bufsize
    }

    *sp = '\0';  //if at the end, add a null terminator character

    list_ele_t *currToRemove = q->head;   //initialize the list element to be removed to the queue's head

    q->head = q->head->next; //set the new head equal to the current head's next
    q->size -=1;   //decrement size because a list element was removed

    if(q->size == 1) {
      q->tail = NULL;     //if the element to be removed is the only one, then the new tail will be null
    }

    free(currToRemove->value);  //free the string
    free(currToRemove); //free the list element

    return true;
}

/*
  Return number of elements in queue.
  Return 0 if q is NULL or empty
 */
int q_size(queue_t *q)
{
    /* You need to write the code for this function */
    /* Remember: It should operate in O(1) time */
    if(q == NULL) {
      return 0;   //if q is null, then size is 0
    }
    return q->size;
}

/*
  Reverse elements in queue
  No effect if q is NULL or empty
  This function should not allocate or free any list elements
  (e.g., by calling q_insert_head, q_insert_tail, or q_remove_head).
  It should rearrange the existing ones.
 */
void q_reverse(queue_t *q)
{
  if(q == NULL || q->size == 0 || q->size == 1) {  //if the queue is empty or if the q has 0 or 1 elements, then no need to Reverse
    return;
  }

  list_ele_t *previousElement = NULL;  //set a previous element holder and initialize it to NULL because in the first iteration of the while loop, the head's next will be set to NULL
  list_ele_t *curr = q->head;          //set a curr list element initialized to the head of the queue
  list_ele_t *nextElement = q->head->next; //set a nextElement list element initialized to the head's next field

  q->tail = q->head; //the queue's new tail will be the queue's old head

  while(nextElement != NULL) { //while their is a next element
    curr->next = previousElement;   //set the current elements next field to the previous curr element
    previousElement = curr;   //set prev equal to curr before we change curr
    curr = nextElement;   //set curr equal to the next element
    nextElement = curr->next;  //set the next element after curr to be curr's next field
  }

  curr->next = previousElement;  //sets the next value of  curr, which should now be head, to the previous e;emenet

  q->head = curr;  //set curr to the head
}
