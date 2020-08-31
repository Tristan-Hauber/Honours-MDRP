#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Aug  6 15:43:43 2020

@author: Tristan
"""

import math
from collections import defaultdict
import itertools
from time import time

from operator import lt, gt

courierData = {} # x y ontime offtime
orderData = {} # x y placementtime restaurant readytime latestLeavingTime maxClickToDoorArrivalTime
restaurantData = {} # x y

grubhubInstance = '0r50t100s1p125'
fileDirectory = 'MealDeliveryRoutingGithub/public_instances/' + grubhubInstance + '/'
programStartTime = time()

def WithoutLetters(string):
    return string.translate({ord(i): None for i in 'abcdefghijklmnopqrstuvwxyz'})

def OpenFile(fileName):
    with open(fileDirectory + fileName) as file:
        # Get lines, dropping header line
        lines = file.read().splitlines()[1:]
        dataDictionary = {}
        for line in lines:
            data = map(WithoutLetters, line.split('\t'))
            data = list(map(int, data))
            dataDictionary[data[0]] = data[1:]
        return dataDictionary

courierData = OpenFile('couriers.txt')
orderData = OpenFile('orders.txt')
restaurantData = OpenFile('restaurants.txt')

def GiveMeAStatusUpdate(label, collectionToDisplayLengthOf):
    print(str(len(collectionToDisplayLengthOf)) + ' ' + label + ' ' + str(time() - programStartTime))

with open(fileDirectory + 'instance_parameters.txt') as instanceParameters:
    instanceParameters.readline().strip()
    parameters = instanceParameters.readline().strip().split('\t')
    travelSpeed = int(parameters[0]) # metres per minute
    pickupServiceTime = int(parameters[1]) # minutes
    dropoffServiceTime = int(parameters[2]) # minutes
    targetClickToDoor = int(parameters[3]) # minutes
    maxClickToDoor = int(parameters[4]) # minutes
    payPerDelivery = int(parameters[5]) # dollars
    minPayPerHour = int(parameters[6]) # dollars

ordersAtRestaurant = {restaurant: [] for restaurant in restaurantData}
for order in orderData:
    ordersAtRestaurant[orderData[order][3]].append(order)

couriersByOffTime = defaultdict(list)
for courier in courierData:
    couriersByOffTime[courierData[courier][3]].append(courier)

def TravelTime(loc1, loc2):
    x1, y1 = loc1[0], loc1[1]
    x2, y2 = loc2[0], loc2[1]
    return math.sqrt((x1-x2)**2 + (y1-y2)**2) / travelSpeed

for order in orderData:
    maxClickToDoorArrivalTime = orderData[order][2] + maxClickToDoor
    travelTime = (pickupServiceTime + dropoffServiceTime) / 2 + TravelTime(restaurantData[orderData[order][3]], orderData[order])
    orderDatum = orderData[order]
    orderData[order].append(maxClickToDoorArrivalTime - travelTime)
    orderData[order].append(maxClickToDoorArrivalTime)

def SomeCompareOperation(op, dictionary, key1, key2, index):
    return op(dictionary[key1][index], dictionary[key2][index])

def SomeCombinedOperation(op1, op2, dictionary, key1, key2, index1, index2):
    return SomeCompareOperation(op1, dictionary, key1, key2, index1) and SomeCompareOperation(op2, dictionary, key1, key2, index2)

def RemoveDominatedSequences(sequences):
    sequencesBySetAndLastOrder = defaultdict(list)
    for sequence in sequences:
        sequencesBySetAndLastOrder[(frozenset(sequence), sequence[-1])].append(sequence)
    dominatedSequences = set()
    for group in sequencesBySetAndLastOrder:
        if len(sequencesBySetAndLastOrder[group]) > 1:
            for (sequence1, sequence2) in itertools.combinations(sequencesBySetAndLastOrder[group],2):
                if SomeCombinedOperation(gt, lt, sequences, sequence1, sequence2, 2, 3):
                    dominatedSequences.add(sequence2)
                elif SomeCombinedOperation(lt, gt, sequences, sequence1, sequence2, 2, 3):
                    dominatedSequences.add(sequence1)
    for sequence in dominatedSequences:
        del sequences[sequence]
    return sequences

orderDeliverySequences = {}
# orderSequence: [restaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime]
for restaurant in restaurantData:
    sequenceLength = 1
    calculatedSequences = {}
    for order in ordersAtRestaurant[restaurant]:
        calculatedSequences[(order,)] = [restaurant, orderData[order][4], orderData[order][5], TravelTime(restaurantData[restaurant], orderData[order]) + (pickupServiceTime + dropoffServiceTime) / 2]
    for sequence in calculatedSequences:
        orderDeliverySequences[sequence] = calculatedSequences[sequence]
    while len(calculatedSequences) > 0:
        sequenceLength += 1
        newSequences = {}
        for sequence in calculatedSequences:
            for order in ordersAtRestaurant[restaurant]:
                if order not in sequence:
                    newSequence = sequence + (order,)
                    totalTravelTime = orderDeliverySequences[sequence][3] + dropoffServiceTime + TravelTime(orderData[sequence[-1]], orderData[order])
                    latestLeavingTime = min(orderDeliverySequences[sequence][2], orderData[order][6] - totalTravelTime)
                    earliestLeavingTime = max(orderDeliverySequences[sequence][1], orderData[order][4])
                    if earliestLeavingTime < latestLeavingTime:
                        newSequences[newSequence] = [restaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime]
        if sequenceLength >= 3:
            newSequences = RemoveDominatedSequences(newSequences)
        calculatedSequences = newSequences
        for sequence in calculatedSequences:
            orderDeliverySequences[sequence] = calculatedSequences[sequence]
GiveMeAStatusUpdate('delivery sequences', orderDeliverySequences)

def CheckDominationPairs(sequenceToCheck, nextRestaurant):
    dominatedSequences = []
    for sequence in groupedPairs[(frozenset(sequenceToCheck), nextRestaurant)]:
        if sequence != sequenceToCheck:
            if SomeCombinedOperation(lt, gt, sequenceNextRestaurantPairs, (sequenceToCheck, nextRestaurant), (sequence, nextRestaurant), 2, 3):
                return [sequenceToCheck]
            if SomeCombinedOperation(gt, lt, sequenceNextRestaurantPairs, (sequenceToCheck, nextRestaurant), (sequence, nextRestaurant), 2, 3):
                dominatedSequences.append(sequence)
    return dominatedSequences

sequenceNextRestaurantPairs = {} # (sequence, nextRestaurant): [restaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime]
groupedPairs = defaultdict(list) # (frozenset(sequence), nextRestaurant): [sequence1, sequence2, sequence3, ...]
for sequence in orderDeliverySequences:
    finishTime = orderDeliverySequences[sequence][1] + orderDeliverySequences[sequence][3]
    for restaurant in restaurantData:
        arrivalAtRestaurant = finishTime + TravelTime(orderData[sequence[-1]], restaurantData[restaurant]) + (dropoffServiceTime + pickupServiceTime) / 2
        for order in ordersAtRestaurant[restaurant]:
            if orderData[order][5] > arrivalAtRestaurant:
                travelTime = orderDeliverySequences[sequence][3] + TravelTime(orderData[sequence[-1]], restaurantData[restaurant]) + (dropoffServiceTime + pickupServiceTime) / 2
                sequenceNextRestaurantPairs[(sequence, restaurant)] = orderDeliverySequences[sequence][:3] + [travelTime]
                groupedPairs[(frozenset(sequence), restaurant)].append(sequence)
                dominatedSequences = CheckDominationPairs(sequence, restaurant)
                for dominatedSequence in dominatedSequences:
                    del sequenceNextRestaurantPairs[(dominatedSequence, restaurant)]
                    groupedPairs[(frozenset(sequence), restaurant)].remove(dominatedSequence)
                break

# sequenceNextRestaurantPairs = {}
# for sequence in orderDeliverySequences:
#     finishTime = orderDeliverySequences[sequence][1] + orderDeliverySequences[sequence][3]
#     for restaurant in restaurantData:
#         arrivalAtRestaurant = finishTime + TravelTime(orderData[sequence[-1]], restaurantData[restaurant]) + (dropoffServiceTime + pickupServiceTime) / 2
#         for order in ordersAtRestaurant[restaurant]:
#             if orderData[order][5] > arrivalAtRestaurant:
#                 travelTime = orderDeliverySequences[sequence][3] + TravelTime(orderData[sequence[-1]], restaurantData[restaurant]) + (dropoffServiceTime + pickupServiceTime) / 2
#                 sequenceNextRestaurantPairs[(sequence, restaurant)] = orderDeliverySequences[sequence][:3] + [travelTime]
#                 break
# GiveMeAStatusUpdate('pre-domination pairs', sequenceNextRestaurantPairs)

# groupedPairs = defaultdict(list)
# for pair in sequenceNextRestaurantPairs:
#     groupedPairs[frozenset(pair[0]), pair[1]].append(pair[0])
# print(max(len(groupedPairs[pair]) for pair in groupedPairs))
# for pair in groupedPairs:
#     dominatedSequences = set()
#     for (sequence1, sequence2) in itertools.combinations(groupedPairs[pair], 2):
#         if SomeCombinedOperation(gt, lt, sequenceNextRestaurantPairs, (sequence1, pair[1]), (sequence2, pair[1]), 2, 3):
#             dominatedSequences.add(sequence2)
#         elif SomeCombinedOperation(lt, gt, sequenceNextRestaurantPairs, (sequence1, pair[1]), (sequence2, pair[1]), 2, 3):
#             dominatedSequences.add(sequence1)
#     for sequence in dominatedSequences:
#         del sequenceNextRestaurantPairs[(sequence, pair[1])]
GiveMeAStatusUpdate('post-domination pairs', sequenceNextRestaurantPairs)

variables = set() # {(offTime1, sequence1, nextRestaurant1), (offTime2, sequence2, nextRestaurant2), ...}
# Main variables
for pair in sequenceNextRestaurantPairs:
    leavingRestaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime = sequenceNextRestaurantPairs[pair]
    earliestArrivalTime = earliestLeavingTime + totalTravelTime
    for offTime in couriersByOffTime:
        if offTime > earliestLeavingTime:
            variableForOffTime = False
            for courier in couriersByOffTime[offTime]:
                courierDatum = courierData[courier]
                if earliestArrivalTime > courierDatum[3]: # check that the courier is still in-shift when arriving at next restaurant
                    continue
                commute = TravelTime(courierDatum, restaurantData[leavingRestaurant])
                if courierDatum[2] + commute + pickupServiceTime / 2 < latestLeavingTime:
                    if courierDatum[3] > earliestLeavingTime:
                        for order in ordersAtRestaurant[pair[1]]:
                            orderDatum = orderData[order]
                            if orderDatum[4] < courierDatum[3] and orderDatum[5] > earliestArrivalTime:
                                variables.add((offTime,) + pair)
                                variableForOffTime = True
                                break
                if variableForOffTime:
                    break
GiveMeAStatusUpdate('main variables', variables)
# Exit variables
# Create sequence-courier (off time) pairs, with nextRestaurant = 0
for sequence in orderDeliverySequences:
    restaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime = orderDeliverySequences[sequence]
    for offTime in couriersByOffTime:
        # off time after earliest ready time
        if offTime > earliestLeavingTime:
            # check that there is a courier that is on for this sequence
            # courier must be able to get to restaurant before latest leaving time
            for courier in couriersByOffTime[offTime]:
                courierDatum = courierData[courier]
                if courierDatum[2] < latestLeavingTime: # added for hopefully a small speed-up?
                    if courierDatum[2] + TravelTime(courierDatum, restaurantData[restaurant]) + pickupServiceTime / 2 < latestLeavingTime:
                        variables.add((offTime, sequence, 0))
                        break
# TODO: Add entry and exit variables
GiveMeAStatusUpdate('main + exit variables', variables)
