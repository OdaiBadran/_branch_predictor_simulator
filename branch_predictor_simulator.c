
#include "bp_api.h"
#include <stdlib.h>
#include <string.h>

#define MAX_PC_BITS 32
#define DEST_LEN 30
#define VALID 1

typedef struct {
    unsigned btbSize_;
    unsigned historySize_;
    unsigned tagSize_;
    unsigned fsmState_;
    bool isGlobalHist_;
    bool isGlobalTable_;
    int Shared_;
    bool* tags_;
    uint32_t* destinations_;
    bool* localHistories_;
    int** localStates_;
    bool* globalHistory_;
    int* globalStates_;
    bool* isEmptyEntry;
    SIM_stats stats_;
} *Predictor;

Predictor pred;

void static initializeHistory(bool* hist2DArray, int length){
    for(int i = 0; i<length; i++)
        hist2DArray[i] = 0;
}
static int power(int x, unsigned int y)
{
    if (y == 0)
        return 1;
    else if (y%2 == 0)
        return power(x, y/2)*power(x, y/2);
    else
        return x*power(x, y/2)*power(x, y/2);
}
static int log2(int x){
    int val = 1;
    int count = 0;
    while(val != x){
        val *= 2;
        ++count;
    }
    return count;
}
static char*  convertHexaToBinary(uint32_t pc){
    char* binary = malloc(32 * sizeof(char));
    strcpy(binary, "");
    int bitCounter = 4;
    int numOfHexaDigits = 0;
    while(pc>0){
        int digit = pc%16;
        ++numOfHexaDigits;
        while(digit>0){
            if(digit%2) strcat(binary,"1");
            else strcat(binary,"0");
            digit /= 2;
            --bitCounter;
        }
        for(int i = 0; i < bitCounter; i++)
            strcat(binary,"0");
        bitCounter = 4;
        pc /= 16;
    }
    char* s = binary + numOfHexaDigits * 4;
    for(int i=0; i<32-(numOfHexaDigits * 4);i++)
        strcat(binary,"0");

    return binary;
}
static bool* convertBinaryStrToBoolArr(char* binaryStr){
    bool* binArr = malloc(sizeof(bool) * MAX_PC_BITS);
    for(int i = 0; i<MAX_PC_BITS; i++) binArr[i] = 0;
    for(int j = 0; j<strlen(binaryStr); j++){
        if(binaryStr[j] == '1') binArr[j] = 1;
        else binArr[j] = 0;
    }
    return binArr;
}

int getIndexInBtb(bool* binArray, int btbSize){
    int decimal = 0;
    for(int i = 2; i < ((int)log2(btbSize) + 2); i++){
        decimal += binArray[i] * power(2,i-2);
    }
    return decimal;
}
int convertBinaryArrToDecimalNum(bool* binArray, int start, int end ){
    int decimal = 0;
    for(int i = start; i < end ; i++){
        decimal += binArray[i] * power(2,i);
    }
    return decimal;
}

static void initializeEntryInBtb(uint32_t pc, uint32_t targetPc, bool* pcInBinaryBool, int indexInBtb){

    pred->destinations_[indexInBtb] = targetPc;
    int j = 0;
    for(int i = 2 + log2(pred->btbSize_);
    i < 2 + log2(pred->btbSize_) + pred->tagSize_; i++){
        pred->tags_[indexInBtb * pred->tagSize_ + j] = pcInBinaryBool[i];
        ++j;
    }
}

static bool* getTagOfPc(bool* pcInBinaryBool){
    int j = 0;
    bool* tagOfPc = malloc(sizeof(pred->tagSize_));
    for(int i = 2 + log2(pred->btbSize_);
        i < 2 + log2(pred->btbSize_) + pred->tagSize_ + 1; i++){
        tagOfPc[j] = pcInBinaryBool[i];
        ++j;
    }
    return tagOfPc;
}

static void shiftRightAndUpdateHist(bool* hist, bool token){
    for(int i =  pred->historySize_ - 1; i > 0; i--) hist[i] = hist[i - 1];
    hist[0] = token;
}

int BP_init(unsigned btbSize, unsigned historySize, unsigned tagSize, unsigned fsmState,
			bool isGlobalHist, bool isGlobalTable, int Shared){

    pred = malloc(sizeof(*pred));
    pred->btbSize_ = btbSize;
    pred->historySize_ = historySize;
    pred->tagSize_ = tagSize;
    pred->fsmState_ = fsmState;
    pred->isGlobalHist_ = isGlobalHist;
    pred->isGlobalTable_ = isGlobalTable;
    pred->Shared_ = Shared;
    pred->tags_ = malloc(pred->btbSize_ * pred->tagSize_* sizeof(bool));
    initializeHistory(pred->tags_, pred->btbSize_ * pred->tagSize_);//meaningless till now
    pred->destinations_ = malloc(pred->btbSize_ * sizeof(uint32_t));
    pred->localHistories_ = NULL;
    pred->localStates_ = NULL;
    pred->globalHistory_ = NULL;
    pred->globalStates_ = NULL;
    pred->isEmptyEntry = malloc(sizeof(bool) * pred->btbSize_);
    pred->stats_.size = 0;
    pred->stats_.br_num = 0;
    pred->stats_.flush_num = 0;
    for(int i = 0; i < pred->btbSize_; i++) pred->isEmptyEntry[i] = 1;
    // Case 1 :
    // local predictor with local table
    if(isGlobalHist == false && isGlobalTable == false){
        pred->localHistories_ = malloc(pred->btbSize_ * pred->historySize_ * sizeof(bool));
        // fill all local histories with zeros
        initializeHistory(pred->localHistories_, pred->btbSize_ * pred->historySize_);
        pred->localStates_ = malloc(sizeof(int*) * pred->btbSize_);
        for(int i = 0; i < pred->btbSize_; i++){
            pred->localStates_[i] = malloc(sizeof(int) * power(2, pred->historySize_));
            // fill all the 2^histSize with fsmState
            for(int j = 0; j < power(2, pred->historySize_); j++)
                pred->localStates_[i][j] = pred->fsmState_;
        }
        return 0;
    }
    if(pred->isGlobalHist_ == true && pred->isGlobalTable_ == false){
        pred->globalHistory_ = malloc(sizeof(bool) * pred->historySize_);
        // fill all local histories with zeros
        initializeHistory(pred->globalHistory_, pred->historySize_);
        pred->localStates_ = malloc(sizeof(int*) * pred->btbSize_);
        for(int i = 0; i < pred->btbSize_; i++) {
            pred->localStates_[i] = malloc(sizeof(int) * power(2, pred->historySize_));
            // fill all the 2^histSize with fsmState
            for (int j = 0; j < power(2, pred->historySize_); j++)
                pred->localStates_[i][j] = pred->fsmState_;
        }
        return 0;
    }
    // Case 2 :
    // local predictor with global table
    if(pred->isGlobalHist_ == false && pred->isGlobalTable_ == true){
        pred->localHistories_ = malloc(pred->btbSize_ * pred->historySize_ * sizeof(bool));
        // fill all local histories with zeros
        initializeHistory(pred->localHistories_, pred->btbSize_ * pred->historySize_);
        pred->globalStates_ = malloc(sizeof(int) * power(2, pred->historySize_));
        for(int j = 0; j < power(2, pred->historySize_); j++)
            pred->globalStates_[j] = pred->fsmState_;
        return 0;
    }
    if(pred->isGlobalHist_ == true && pred->isGlobalTable_ == true){
        pred->globalHistory_ = malloc(sizeof(bool) * pred->historySize_);
        // fill all local histories with zeros
        initializeHistory(pred->globalHistory_, pred->historySize_);
        pred->globalStates_ = malloc(sizeof(int) * power(2, pred->historySize_));
        for(int j = 0; j < power(2, pred->historySize_); j++)
            pred->globalStates_[j] = pred->fsmState_;
        return 0;
    }

	return -1;
}

bool BP_predict(uint32_t pc, uint32_t *dst){
    if(pred->isGlobalHist_ == false && pred->isGlobalTable_ == false) {
         // first convert pc from hexa to boolean representation
         char* pcInBinaryString = convertHexaToBinary(pc);
         bool* pcInBinaryBool = convertBinaryStrToBoolArr(pcInBinaryString);
         bool *tagInBinaryBool = getTagOfPc(pcInBinaryBool);

         // calculate the index of entry in BTB according to pc
         int indexInBtb = getIndexInBtb(pcInBinaryBool,pred->btbSize_);

         // check wither this entry is empty
         if(pred->isEmptyEntry[indexInBtb]){
             *dst = pc + 4;
             free(pcInBinaryString);
             free(pcInBinaryBool);
             free(tagInBinaryBool);
             return false;
         }
        // convert tag on indexInBtb to  decimal if possible otherwise tag = -1
        int tag1 = (!pred->isEmptyEntry[indexInBtb]) ? convertBinaryArrToDecimalNum
                (pred->tags_ + (indexInBtb * pred->tagSize_), 0, pred->tagSize_) : -1;
        // convert tag of the given pc to decimal
        int tag2 = convertBinaryArrToDecimalNum(tagInBinaryBool, 0, pred->tagSize_);
        if(tag1 == tag2){
            // check wither the prediction is Taken or not-Taken and fill dst accordingly
            int indexOfFsm = convertBinaryArrToDecimalNum(pred->localHistories_ +
                    (indexInBtb * pred->historySize_), 0, pred->historySize_);
            int state = pred->localStates_[indexInBtb][indexOfFsm];
            *dst = ((state == 3) || (state == 2)) ? pred->destinations_[indexInBtb] : pc + 4;
            free(pcInBinaryString);
            free(pcInBinaryBool);
            free(tagInBinaryBool);
            return ((state == 3) || (state == 2));
        } // otherwise the pcs are different and tags are different but mapped to same entry:
        *dst = pc + 4;
        free(pcInBinaryString);
        free(pcInBinaryBool);
        free(tagInBinaryBool);
        return false;
    }
    if(pred->isGlobalHist_ == true && pred->isGlobalTable_ == false) {
        char* pcInBinaryString = convertHexaToBinary(pc);
        bool* pcInBinaryBool = convertBinaryStrToBoolArr(pcInBinaryString);
        bool *tagInBinaryBool = getTagOfPc(pcInBinaryBool);
        int indexInBtb = getIndexInBtb(pcInBinaryBool,pred->btbSize_);
        // check wither this entry is empty
        if(pred->isEmptyEntry[indexInBtb]){
            *dst = pc + 4;
            free(pcInBinaryString);
            free(pcInBinaryBool);
            free(tagInBinaryBool);
            return false;
        }
        // convert tag on indexInBtb to  decimal if possible otherwise tag = -1
        int tag1 = (!pred->isEmptyEntry[indexInBtb]) ? convertBinaryArrToDecimalNum
                (pred->tags_ + (indexInBtb * pred->tagSize_), 0, pred->tagSize_) : -1;
        // convert tag of the given pc to decimal
        int tag2 = convertBinaryArrToDecimalNum(tagInBinaryBool, 0, pred->tagSize_);
        if(tag1 == tag2){
            int indexOfFsm = convertBinaryArrToDecimalNum(pred->globalHistory_,
                                                          0, pred->historySize_);
            int state = pred->localStates_[indexInBtb][indexOfFsm];
            *dst = ((state == 3) || (state == 2)) ? pred->destinations_[indexInBtb] : pc + 4;
            free(pcInBinaryString);
            free(pcInBinaryBool);
            free(tagInBinaryBool);
            return ((state == 3) || (state == 2));
        } // otherwise the pc is unrecognized in the btb so considered as new:
        *dst = pc + 4;
        free(pcInBinaryString);
        free(pcInBinaryBool);
        free(tagInBinaryBool);
        return false;

    }
    if(pred->isGlobalHist_ == false && pred->isGlobalTable_ == true) {
            // first convert pc from hexa to boolean representation
            char* pcInBinaryString = convertHexaToBinary(pc);
            bool* pcInBinaryBool = convertBinaryStrToBoolArr(pcInBinaryString);
            bool *tagInBinaryBool = getTagOfPc(pcInBinaryBool);

            // calculate the index of entry in BTB according to pc
            int indexInBtb = getIndexInBtb(pcInBinaryBool,pred->btbSize_);

            // check wither this entry is empty
            if(pred->isEmptyEntry[indexInBtb]){
                *dst = pc + 4;
                free(pcInBinaryString);
                free(pcInBinaryBool);
                free(tagInBinaryBool);
                return false;
            }
            int tag1 = (!pred->isEmptyEntry[indexInBtb]) ? convertBinaryArrToDecimalNum
                (pred->tags_ + (indexInBtb * pred->tagSize_), 0, pred->tagSize_) : -1;
              // convert tag of the given pc to decimal
            int tag2 = convertBinaryArrToDecimalNum(tagInBinaryBool, 0, pred->tagSize_);
            if(tag1 == tag2){
                if(pred->Shared_ == 0){                //not_using_share
                    int indexOfFsm = convertBinaryArrToDecimalNum(pred->localHistories_ +
                            (indexInBtb * pred->historySize_) , 0, pred->historySize_);

                    int state = pred->globalStates_[indexOfFsm];
                    *dst = ((state == 3) || (state == 2)) ? pred->destinations_[indexInBtb] : pc + 4;
                    free(pcInBinaryString);
                    free(pcInBinaryBool);
                    free(tagInBinaryBool);
                    return ((state == 3) || (state == 2));
                }
                if(pred->Shared_ == 1 || pred->Shared_ == 2){
                    int xorPcIndex = (pred->Shared_ == 1) ? 2 : 16;
                    bool* xorShareResult = malloc(sizeof(bool) * pred->historySize_);
                    for(int i = 0; i < pred->historySize_; i++){
                        xorShareResult[i] = ((pred->localHistories_ + (indexInBtb *
                               pred->historySize_))[i] ^ pcInBinaryBool[xorPcIndex + i]);

                    }
                    int indexOfFsm = convertBinaryArrToDecimalNum(xorShareResult
                            , 0, pred->historySize_);
                    int state = pred->globalStates_[indexOfFsm];
                    *dst = ((state == 3) || (state == 2)) ? pred->destinations_[indexInBtb] : pc + 4;
                    free(pcInBinaryString);
                    free(pcInBinaryBool);
                   // free(xorShareResult);
                    free(tagInBinaryBool);
                    return ((state == 3) || (state == 2));
                }
            }
             // otherwise means the two pcs are different and mapped to the same entry:
             *dst = pc + 4;
             free(pcInBinaryString);
             free(pcInBinaryBool);
             free(tagInBinaryBool);
             return false;
    }
    if(pred->isGlobalHist_ == true && pred->isGlobalTable_ == true) {
        char* pcInBinaryString = convertHexaToBinary(pc);
        bool* pcInBinaryBool = convertBinaryStrToBoolArr(pcInBinaryString);
        bool *tagInBinaryBool = getTagOfPc(pcInBinaryBool);
        int indexInBtb = getIndexInBtb(pcInBinaryBool,pred->btbSize_);
        // check wither this entry is empty
        if(pred->isEmptyEntry[indexInBtb]){
            *dst = pc + 4;
            free(pcInBinaryString);
            free(pcInBinaryBool);
            free(tagInBinaryBool);
            return false;
        }//
        // convert tag on indexInBtb to  decimal if possible otherwise tag = -1
        int tag1 = (!pred->isEmptyEntry[indexInBtb]) ? convertBinaryArrToDecimalNum
                (pred->tags_ + (indexInBtb * pred->tagSize_), 0, pred->tagSize_) : -1;
        // convert tag of the given pc to decimal
        int tag2 = convertBinaryArrToDecimalNum(tagInBinaryBool, 0, pred->tagSize_);
        if(tag1 == tag2){
            if(pred->Shared_ == 0){
                int indexOfFsm = convertBinaryArrToDecimalNum(pred->globalHistory_
                        , 0, pred->historySize_);
                int state = pred->globalStates_[indexOfFsm];
                *dst = ((state == 3) || (state == 2)) ? pred->destinations_[indexInBtb] : pc + 4;
                free(pcInBinaryString);
                free(pcInBinaryBool);
                free(tagInBinaryBool);
                return ((state == 3) || (state == 2));
            }
            if(pred->Shared_ == 1 || pred->Shared_ == 2){
                int xorPcIndex = (pred->Shared_ == 1) ? 2 : 16;
                bool xorShareResult[pred->historySize_];
                for(int i = 0; i < pred->historySize_; i++){
                    xorShareResult[i] = (pred->globalHistory_[i] ^
                                         pcInBinaryBool[xorPcIndex + i]);
                }
                int indexOfFsm = convertBinaryArrToDecimalNum(xorShareResult
                        , 0, pred->historySize_);
                int state = pred->globalStates_[indexOfFsm];
                *dst = ((state == 3) || (state == 2)) ? pred->destinations_[indexInBtb] : pc + 4;
                free(pcInBinaryString);
                free(pcInBinaryBool);
                free(tagInBinaryBool);
                //free(xorShareResult);
                return ((state == 3) || (state == 2));
            }
        } //otherwise the pc is unreconized so considered as new :
        *dst = pc + 4;
        free(pcInBinaryString);
        free(pcInBinaryBool);
        free(tagInBinaryBool);
        return false;
    }
    return false; // should not get here at this stage
}

void BP_update(uint32_t pc, uint32_t targetPc, bool taken, uint32_t pred_dst) {

    ++pred->stats_.br_num;
    if (taken) {
        pred->stats_.flush_num = (targetPc == pred_dst) ?
                                 pred->stats_.flush_num : pred->stats_.flush_num + 1;
    } else {
        pred->stats_.flush_num = (pc + 4 == pred_dst) ?
                                 pred->stats_.flush_num : pred->stats_.flush_num + 1;
    }
    if (pred->isGlobalHist_ == false && pred->isGlobalTable_ == false) {
        char *pcInBinaryString = convertHexaToBinary(pc);
        bool *pcInBinaryBool = convertBinaryStrToBoolArr(pcInBinaryString);
        bool *tagInBinaryBool = getTagOfPc(pcInBinaryBool);
        int indexInBtb = getIndexInBtb(pcInBinaryBool, pred->btbSize_);
        pred->destinations_[indexInBtb] = targetPc;

        // convert tag on indexInBtb to  decimal if possible otherwise tag = -1
        int tag1 = (!pred->isEmptyEntry[indexInBtb]) ? convertBinaryArrToDecimalNum
                (pred->tags_ + (indexInBtb * pred->tagSize_),
                        0, pred->tagSize_) : -1;
        // convert tag of the given pc to decimal
        int tag2 = convertBinaryArrToDecimalNum(tagInBinaryBool, 0, pred->tagSize_);

        // check if the two tags are equal means that :
        // they are the same pc or they are different pcs with equal tags
        if (tag1 == tag2) {
            int indexOfFsm = convertBinaryArrToDecimalNum(
                    pred->localHistories_ + (indexInBtb * pred->historySize_)
                    , 0, pred->historySize_);
            int state = pred->localStates_[indexInBtb][indexOfFsm];
            state = (taken) ? state + 1 : state - 1;
            state = (state > 3) ? 3 : state;
            state = (state < 0) ? 0 : state;
            pred->localStates_[indexInBtb][indexOfFsm] = state;
            shiftRightAndUpdateHist(pred->localHistories_ +
            (indexInBtb * pred->historySize_), taken);
            free(pcInBinaryString);
            free(pcInBinaryBool);
            free(tagInBinaryBool);
            return;
        }
        // otherwise : the entry of indexInBtb is empty or  they are different pcs :
        initializeEntryInBtb(pc, targetPc, pcInBinaryBool, indexInBtb);
        //initialize states to fsmState :
        for(int j = 0; j < power(2, pred->historySize_); j++)
            pred->localStates_[indexInBtb][j] = pred->fsmState_;

        //shift all history bit and add taken in histloc[0]
        // got to suitable fsm and do +1 or -1 accordingly
        initializeHistory(pred->localHistories_ +
        indexInBtb * pred->historySize_, pred->historySize_);
        int indexOfFsm = convertBinaryArrToDecimalNum(
                pred->localHistories_ + indexInBtb * pred->historySize_
                , 0, pred->historySize_);
        int state = pred->localStates_[indexInBtb][indexOfFsm];
        state = (taken) ? state + 1 : state - 1;
        state = (state > 3) ? 3 : state;
        state = (state < 0) ? 0 : state;
        pred->localStates_[indexInBtb][indexOfFsm] = state;
        shiftRightAndUpdateHist(pred->localHistories_ +
        indexInBtb * pred->historySize_, taken);
        pred->isEmptyEntry[indexInBtb] = false;
        free(pcInBinaryString);
        free(pcInBinaryBool);
        free(tagInBinaryBool);
        return;
    }
    if (pred->isGlobalHist_ == true && pred->isGlobalTable_ == false) {
        char *pcInBinaryString = convertHexaToBinary(pc);
        bool *pcInBinaryBool = convertBinaryStrToBoolArr(pcInBinaryString);
        bool *tagInBinaryBool = getTagOfPc(pcInBinaryBool);
        int indexInBtb = getIndexInBtb(pcInBinaryBool, pred->btbSize_);
        pred->destinations_[indexInBtb] = targetPc;
        // convert tag on indexInBtb to  decimal if possible otherwise tag = -1
        int tag1 = (!pred->isEmptyEntry[indexInBtb]) ? convertBinaryArrToDecimalNum
                (pred->tags_ + (indexInBtb * pred->tagSize_),
                 0, pred->tagSize_) : -1;
        // convert tag of the given pc to decimal
        int tag2 = convertBinaryArrToDecimalNum(tagInBinaryBool, 0, pred->tagSize_);

        // check if the two tags are equal means that :
        // they are the same pc or they are different pcs with equal tags
        if (tag1 == tag2){
            int indexOfFsm = convertBinaryArrToDecimalNum(pred->globalHistory_
                    , 0, pred->historySize_);
            int state = pred->localStates_[indexInBtb][indexOfFsm];
            state = (taken) ? state + 1 : state - 1;
            state = (state > 3) ? 3 : state;
            state = (state < 0) ? 0 : state;
            pred->localStates_[indexInBtb][indexOfFsm] = state;
            shiftRightAndUpdateHist(pred->globalHistory_, taken);
            free(pcInBinaryString);
            free(pcInBinaryBool);
            free(tagInBinaryBool);
            return;
        }
        // otherwise : the entry of indexInBtb is empty or  they are different pcs :
        initializeEntryInBtb(pc, targetPc, pcInBinaryBool, indexInBtb);
        //initialize states to fsmState :
        for(int j = 0; j < power(2, pred->historySize_); j++)
            pred->localStates_[indexInBtb][j] = pred->fsmState_;
        int indexOfFsm = convertBinaryArrToDecimalNum(pred->globalHistory_
                , 0, pred->historySize_);
        int state = pred->localStates_[indexInBtb][indexOfFsm];
        state = (taken) ? state + 1 : state - 1;
        state = (state > 3) ? 3 : state;
        state = (state < 0) ? 0 : state;
        pred->localStates_[indexInBtb][indexOfFsm] = state;
        shiftRightAndUpdateHist(pred->globalHistory_, taken);
        pred->isEmptyEntry[indexInBtb] = false;
        free(pcInBinaryString);
        free(pcInBinaryBool);
        free(tagInBinaryBool);
        return;
    }

    if (pred->isGlobalHist_ == false && pred->isGlobalTable_ == true) {
        char *pcInBinaryString = convertHexaToBinary(pc);
        bool *pcInBinaryBool = convertBinaryStrToBoolArr(pcInBinaryString);
        bool *tagInBinaryBool = getTagOfPc(pcInBinaryBool);
        int indexInBtb = getIndexInBtb(pcInBinaryBool, pred->btbSize_);
        pred->destinations_[indexInBtb] = targetPc;

        // convert tag on indexInBtb to  decimal if possible otherwise tag = -1
        int tag1 = (!pred->isEmptyEntry[indexInBtb]) ? convertBinaryArrToDecimalNum
                (pred->tags_ + (indexInBtb * pred->tagSize_), 0, pred->tagSize_) : -1;
        // convert tag of the given pc to decimal
        int tag2 = convertBinaryArrToDecimalNum(tagInBinaryBool, 0, pred->tagSize_);

        // check if the two tags are equal means that :
        // they are the same pc or they are different pcs with equal tags
        if (tag1 == tag2) {
            if (pred->Shared_ == 0) {
                int indexOfFsm = convertBinaryArrToDecimalNum(pred->localHistories_
                        + indexInBtb * pred->historySize_, 0, pred->historySize_);
                int state = pred->globalStates_[indexOfFsm];
                state = (taken) ? state + 1 : state - 1;
                state = (state > 3) ? 3 : state;
                state = (state < 0) ? 0 : state;
                pred->globalStates_[indexOfFsm] = state;
                shiftRightAndUpdateHist(pred->localHistories_ +
                indexInBtb * pred->historySize_, taken);
                free(pcInBinaryString);
                free(pcInBinaryBool);
                free(tagInBinaryBool);
                return;
            }
            if (pred->Shared_ == 1 || pred->Shared_ == 2) {
                int xorPcIndex = (pred->Shared_ == 1) ? 2 : 16;
                bool xorShareResult[pred->historySize_];
                for (int i = 0; i < pred->historySize_; i++) {
                    xorShareResult[i] = ((pred->localHistories_ + (indexInBtb *
                            pred->historySize_))[i] ^ pcInBinaryBool[xorPcIndex + i]);

                }
                int indexOfFsm = convertBinaryArrToDecimalNum(xorShareResult, 0, pred->historySize_);
                int state = pred->globalStates_[indexOfFsm];
                state = (taken) ? state + 1 : state - 1;
                state = (state > 3) ? 3 : state;
                state = (state < 0) ? 0 : state;
                pred->globalStates_[indexOfFsm] = state;
                shiftRightAndUpdateHist(pred->localHistories_ +
                indexInBtb * pred->historySize_, taken);
                free(pcInBinaryString);
                free(pcInBinaryBool);
                free(tagInBinaryBool);
               // free(xorShareResult);
                return;
            }
        }
        // otherwise : the entry of indexInBtb is empty or  they are different pcs :
        initializeEntryInBtb(pc, targetPc, pcInBinaryBool, indexInBtb);

        //shift all history bit and add taken in histloc[0]
        // got to suitable fsm and do +1 or -1 accordingly
        initializeHistory(pred->localHistories_ +
        indexInBtb * pred->historySize_, pred->historySize_);
        if(pred->Shared_ == 0){
            int indexOfFsm = convertBinaryArrToDecimalNum(
                    pred->localHistories_ + indexInBtb * pred->historySize_
                    , 0, pred->historySize_);
            int state = pred->globalStates_[indexOfFsm];
            state = (taken) ? state + 1 : state - 1;
            state = (state > 3) ? 3 : state;
            state = (state < 0) ? 0 : state;
            pred->globalStates_[indexOfFsm] = state;
            shiftRightAndUpdateHist(pred->localHistories_ +
            indexInBtb * pred->historySize_, taken);
            pred->isEmptyEntry[indexInBtb] = false;
            free(pcInBinaryString);
            free(pcInBinaryBool);
            free(tagInBinaryBool);
            return;
        }
        if(pred->Shared_ == 1 || pred->Shared_ == 2){
            int xorPcIndex = (pred->Shared_ == 1) ? 2 : 16;
            bool xorShareResult[pred->historySize_];
            for (int i = 0; i < pred->historySize_; i++) {
                xorShareResult[i] = ((pred->localHistories_ +
                        indexInBtb * pred->historySize_)[i] ^ pcInBinaryBool[xorPcIndex + i]);

            }
            int indexOfFsm = convertBinaryArrToDecimalNum(xorShareResult,
                    0, pred->historySize_);
            int state = pred->globalStates_[indexOfFsm];
            state = (taken) ? state + 1 : state - 1;
            state = (state > 3) ? 3 : state;
            state = (state < 0) ? 0 : state;
            pred->globalStates_[indexOfFsm] = state;
            shiftRightAndUpdateHist(pred->localHistories_ +
            indexInBtb * pred->historySize_, taken);
            pred->isEmptyEntry[indexInBtb] = false;
            free(pcInBinaryString);
            free(pcInBinaryBool);
            free(tagInBinaryBool);
           // free(xorShareResult);
            return;
        }
    }
    if (pred->isGlobalHist_ == true && pred->isGlobalTable_ == true) {
        char *pcInBinaryString = convertHexaToBinary(pc);
        bool *pcInBinaryBool = convertBinaryStrToBoolArr(pcInBinaryString);
        bool *tagInBinaryBool = getTagOfPc(pcInBinaryBool);
        int indexInBtb = getIndexInBtb(pcInBinaryBool,pred->btbSize_);
        pred->destinations_[indexInBtb] = targetPc;
        // convert tag on indexInBtb to  decimal if possible otherwise tag = -1
        int tag1 = (!pred->isEmptyEntry[indexInBtb]) ? convertBinaryArrToDecimalNum
                (pred->tags_ + (indexInBtb * pred->tagSize_),
                 0, pred->tagSize_) : -1;
        // convert tag of the given pc to decimal
        int tag2 = convertBinaryArrToDecimalNum(tagInBinaryBool, 0, pred->tagSize_);

        // check if the two tags are equal means that :
        // they are the same pc or they are different pcs with equal tags
        if (tag1 == tag2){
            if(pred->Shared_ == 0){
                int indexOfFsm = convertBinaryArrToDecimalNum(pred->globalHistory_
                        , 0, pred->historySize_);
                int state = pred->globalStates_[indexOfFsm];
                state = (taken) ? state + 1 : state - 1;
                state = (state > 3) ? 3 : state;
                state = (state < 0) ? 0 : state;
                pred->globalStates_[indexOfFsm] = state;
                shiftRightAndUpdateHist(pred->globalHistory_, taken);
                free(pcInBinaryString);
                free(tagInBinaryBool);
                free(pcInBinaryBool);
                return;
            }
            if(pred->Shared_ == 1 || pred->Shared_ == 2){
                int xorPcIndex = (pred->Shared_ == 1) ? 2 : 16;
                bool xorShareResult[pred->historySize_];
                for(int i = 0; i < pred->historySize_; i++){
                    xorShareResult[i] = (pred->globalHistory_[i] ^
                                         pcInBinaryBool[xorPcIndex + i]);
                }
                int indexOfFsm = convertBinaryArrToDecimalNum(xorShareResult
                        , 0, pred->historySize_);
                int state = pred->globalStates_[indexOfFsm];
                state = (taken) ? state + 1 : state - 1;
                state = (state > 3) ? 3 : state;
                state = (state < 0) ? 0 : state;
                pred->globalStates_[indexOfFsm] = state;
                shiftRightAndUpdateHist(pred->globalHistory_, taken);
                free(pcInBinaryString);
                free(pcInBinaryBool);
                free(tagInBinaryBool);
                //free(xorShareResult);
                return;
            }
        }
        // otherwise : the entry of indexInBtb is empty or  they are different pcs :
        initializeEntryInBtb(pc, targetPc, pcInBinaryBool, indexInBtb);
        if(pred->Shared_ == 0){
            int indexOfFsm = convertBinaryArrToDecimalNum(pred->globalHistory_
                    , 0, pred->historySize_);
            int state = pred->globalStates_[indexOfFsm];
            state = (taken) ? state + 1 : state - 1;
            state = (state > 3) ? 3 : state;
            state = (state < 0) ? 0 : state;
            pred->globalStates_[indexOfFsm] = state;
            shiftRightAndUpdateHist(pred->globalHistory_, taken);
            pred->isEmptyEntry[indexInBtb] = false;
            free(tagInBinaryBool);
            free(pcInBinaryString);
            free(pcInBinaryBool);
            return;
        }
        if(pred->Shared_ == 1 || pred->Shared_ == 2){
            int xorPcIndex = (pred->Shared_ == 1) ? 2 : 16;
            bool xorShareResult[pred->historySize_];
            for(int i = 0; i < pred->historySize_; i++){
                xorShareResult[i] = (pred->globalHistory_[i] ^
                                     pcInBinaryBool[xorPcIndex + i]);
            }
            int indexOfFsm = convertBinaryArrToDecimalNum(xorShareResult
                    , 0, pred->historySize_);
            int state = pred->globalStates_[indexOfFsm];
            state = (taken) ? state + 1 : state - 1;
            state = (state > 3) ? 3 : state;
            state = (state < 0) ? 0 : state;
            pred->globalStates_[indexOfFsm] = state;
            shiftRightAndUpdateHist(pred->globalHistory_, taken);
            pred->isEmptyEntry[indexInBtb] = false;
            free(tagInBinaryBool);
            free(pcInBinaryString);
            free(pcInBinaryBool);
            //free(xorShareResult);
            return;
        }

    }
}

void BP_GetStats(SIM_stats *curStats) {
    curStats->flush_num = pred->stats_.flush_num;
    curStats->br_num = pred->stats_.br_num;
    if (pred->isGlobalHist_ == false && pred->isGlobalTable_ == false) {
        curStats->size = pred->btbSize_ * (pred->tagSize_ + VALID +
                DEST_LEN + pred->historySize_ + (2 * power(2, pred->historySize_)));
        return;
    }
    if (pred->isGlobalHist_ == false && pred->isGlobalTable_ == true) {
        curStats->size = pred->btbSize_ * (pred->tagSize_ + VALID
                + DEST_LEN + pred->historySize_) + (2 * power(2, pred->historySize_));
        return;
    }
    if (pred->isGlobalHist_ == true && pred->isGlobalTable_ == true) {
        curStats->size = (pred->btbSize_ * (pred->tagSize_ + VALID + DEST_LEN)) +
                pred->historySize_ + (2 * power(2, pred->historySize_));
        return;
    }
    if (pred->isGlobalHist_ == true && pred->isGlobalTable_ == false) {
        curStats->size = pred->btbSize_ * (pred->tagSize_ + VALID +
                DEST_LEN  + (2 * power(2, pred->historySize_))) + pred->historySize_;
        return;
    }
    free(pred->tags_);
    free(pred->destinations_);
    free(pred->isEmptyEntry);
    free(pred->globalHistory_);
    free(pred->globalStates_);
    free(pred->localHistories_);
    for (int i = 0; i < pred->btbSize_; i++)
        free(pred->localStates_[i]);
    free(pred->localStates_);
}

