import numpy
import matplotlib.pyplot
import os
import time
import itertools
import re
import math

import nltk
from nltk.corpus import stopwords
from nltk.stem import WordNetLemmatizer
from nltk import pos_tag
'''
nltk.download('stopwords') #TODO: do i need to download every time??
nltk.download('punkt_tab')      
nltk.download('wordnet')    
nltk.download('omw-1.4') 
nltk.download('averaged_perceptron_tagger_eng') '''

def get_wordnet_pos(tag):
    if tag.startswith('J'):
        return 'a'
    elif tag.startswith('V'):
        return 'v'
    elif tag.startswith('N'):
        return 'n'
    elif tag.startswith('R'):
        return 'r'
    else:
        return 'n'
    
def normalize(line): 
    ret = []
    tokenizer = nltk.tokenize.RegexpTokenizer(r'\w+') #this does capital and lowercase letters, numbers, and_
    lemmatizer = WordNetLemmatizer() #make all same part of speech
    stop_words = set(stopwords.words('english'))
    words = tokenizer.tokenize(line) #TODO: should i take numbers out
    i = 0
    while i < len(words):
        words[i] = words[i].lower()
        if words[i] in stop_words:
            words.pop(i)
        else:
            i = i + 1 #maybe i could use iterTools or smth, but this works
    tagged_words = pos_tag(words) #TODO: watch the order here, and then my report wants to hear about it
    for word, tag in tagged_words:
        ret.append(lemmatizer.lemmatize(word, get_wordnet_pos(tag)))
    return ret

def processFile(filename, i):
    file = open(filename, "r")
    numSents = 0
    for line in file:
        if line != '\n':
            numSents = numSents + 1
            words = normalize(line)
            for word in words:
                if word in vocab:
                    vocab[word][i] = vocab[word][i] + 1
                else:
                    vocab[word] = [0, 0, 0, 0] #bio, econ, history, phys
                    vocab[word][i] = 1
    sentCount[i] = numSents
    file.close()

def processSentiment(filename):
    file = open(filename, "r")
    numPos = 0
    numNeg = 0
    for line in file:
        if line != '\n':
            words = normalize(line)[:-1]
            i = int(line[-2]) #last thing besides \n in sentence is rating 0 for neg, 1 for pos
            if i == 0:
                numNeg = numNeg + 1
            else:
                numPos = numPos + 1
            for word in words:
                if word in sentiment_vocab:
                    sentiment_vocab[word][i] = sentiment_vocab[word][i] + 1
                else:
                    sentiment_vocab[word] = [0, 0] #neg, pos
                    sentiment_vocab[word][i] = 1 
    sentiment_sentCount[0] = sentiment_sentCount[0] + numNeg
    sentiment_sentCount[1] = sentiment_sentCount[1] + numPos
    file.close()

vocab = {} #key is word, list of occurences per discipline in order biology, econ, history, physics
sentCount = [0, 0, 0, 0] #same order bio, econ, history, phys TODO: this is manual, a bit bad
processFile('training_biology.txt', 0) 
processFile('training_economics.txt', 1)
processFile('training_history.txt', 2)
processFile('training_physics.txt', 3)
totalSents = numpy.sum(sentCount)

sentiment_vocab = {} #TODO: i could write a wrapper function so that i don't have to rewrite these methods so much
sentiment_sentCount = [0, 0]
processSentiment('sentiment+labelled+sentences/amazon_cells_labelled.txt')
processSentiment('sentiment+labelled+sentences/imdb_labelled.txt')
processSentiment('sentiment+labelled+sentences/yelp_labelled.txt')
sentiment_totalSents = numpy.sum(sentiment_sentCount)

for word in vocab:
    for i in range(len(vocab[word])):
        vocab[word][i] = vocab[word][i] + 1 #laplacian smoothing
        vocab[word][i] = vocab[word][i] / sentCount[i] #probabilities


for word in sentiment_vocab:
    for i in range(len(sentiment_vocab[word])):
        sentiment_vocab[word][i] = sentiment_vocab[word][i] + 1 #laplacian smoothing
        sentiment_vocab[word][i] = sentiment_vocab[word][i] / sentiment_sentCount[i] #probabilities

#TODO: what if i stored the vocab between runs??

results = []
for i in range(4):
    results.append([[], [], [], []]) #TODO: this is a bit manual, bad

sentiment_results = []
for i in range(2):
    sentiment_results.append([[], []])


file = open("testing_data.txt", "r")
#for line in file:
if True:
    line = "The human genome project was a major milestone in modern science."
    probs = [sentCount[0] / totalSents, sentCount[1] / totalSents, sentCount[2] / totalSents, sentCount[3] / totalSents] #TODO: this is manual, unnecessary
    words = normalize(line)
    for word in words: #TODO: should skip the first one bc its the answer key, luckily its not in vocab anyway
        if word in vocab:
            for i in range(len(probs)):
                probs[i] = probs[i] + numpy.log(vocab[word][i]) 
    if words[0] == "biology": #TODO: id love to get this from the line so normalize doesn't screw with it
        answer = 0
    elif words[0] == "economics":
        answer = 1
    elif words[0] == 'world':
        answer = 2
    else:
        answer = 3
    results[answer][probs.index(max(probs))].append(line)

sentiment_file = open("testing_sentiment.txt", "r")
#for line in sentiment_file:
if True:
    line = "In other words, the content level of this film is enough to easily fill a dozen other films."
    probs = [sentiment_sentCount[0] / sentiment_totalSents, sentiment_sentCount[1] / sentiment_totalSents] #TODO: this is manual, unnecessary
    words = normalize(line)
    for word in words: 
        if word in sentiment_vocab:
            for i in range(len(probs)):
                probs[i] = probs[i] + numpy.log(sentiment_vocab[word][i]) #TODO: what about that first probability??
    if words[-1] == "0":
        answer = 0
    else:
        answer = 1
    sentiment_results[answer][probs.index(max(probs))].append(line)

print(results[0][1])
print()
print("answer: b e h p")
for row in results:
    print("guesses:", end="")
    for col in row:
        print(str(len(col)), end=" ")
    print()

print(sentiment_results[1][0])
print()
print("answer: + -")
for row in sentiment_results:
    print("guesses:", end="")
    for col in row:
        print(str(len(col)), end=" ")
    print()