#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Aug  6 15:43:43 2020
@author: Tristan
"""





# Program outline
# Done: Import data
# Done: If desired, have the ability to cut out some of the data
# Done: Find all order sequences
# Done: Dominate order sequences
# Done: Find all sequence-restaurant pairs
# Done: Dominate sequence-restaurant pairs
# Done: Create untimed arcs
# Done: Create model nodes
# Done: Convert untimed arcs to timed arcs
# Done: Add model variables
# Done: Add model constraints
# Done: Solve linear model
# Done: Add valid inequality cuts
# Done: Solve integer model
# Done: Add illegal path elimination constraints in callback

# Improvements:
# TODO: Put sequence + pair domination into the one function
# TODO: Revise code to ensure correctness
# TODO: Add an entry untimed arc for every courier, not just every group





import math
from collections import defaultdict
import itertools
from time import time
from gurobipy import Model, quicksum, GRB
import random
from operator import lt, gt





courierData = {} # courier: [x, y, ontime, offtime]
orderData = {} # order: [x, y, placementtime, restaurant, readytime, latestLeavingTime, maxClickToDoorArrivalTime]
restaurantData = {} # restaurant: [x, y]





sequenceData = {} # orderSequence: [placementRestaurant, earliestDepartureTime, latestDepartureTime, totalTravelTime]
sequenceNextRestaurantData = {} # (sequence, nextRestaurant): [placementRestaurant, earliestDepartureTime, latestDepartureTime, totalTravelTime]
untimedArcData = {} # (courierGroup, sequence, nextRestaurant): [placementRestaurant, earliestDepartureTime, latestDepartureTime, totalTravelTime]





grubhubInstance = '0o50t100s1p125'
fileDirectory = 'MealDeliveryRoutingGithub/public_instances/' + grubhubInstance + '/'
programStartTime = time()





nodeTimeInterval = 8
# minutes between nodes
groupCouriersByOffTime = True
groupCouriersByOnTime = False
orderProportion = 1
seed = 1
globalNodeIntervals = True
addValidInequalityConstraints = True
addVIRecursively = True
limitBundlesToSizeOne = False





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
print(str(len(courierData)) + ' couriers')
print(str(len(orderData)) + ' orders')
print(str(len(restaurantData)) + ' restaurants')





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





if orderProportion < 1.0:
    random.seed(seed)
    totalOrderCount = len(orderData)
    restaurantsRemoved = []
    while len(orderData) > totalOrderCount * orderProportion:
        removedRestaurant = random.choice(list(restaurantData.keys()))
        for order in ordersAtRestaurant[removedRestaurant]:
            del orderData[order]
        del ordersAtRestaurant[removedRestaurant]
        del restaurantData[removedRestaurant]
        restaurantsRemoved.append(removedRestaurant)
    print()
    print('Seed = ' + str(seed))
    print('Removed restaurants ' + str(restaurantsRemoved))
    print('Now at ' + str(len(orderData)) + ' orders, down from ' + str(totalOrderCount))
    print()
        



courierGroups = {}
if groupCouriersByOffTime:
    if not groupCouriersByOnTime:
        for courier in courierData:
            offTime = courierData[courier][3]
            if offTime not in courierGroups:
                courierGroups[offTime] = [[], offTime]
            courierGroups[offTime][0].append(courier)
    else:
        for courier in courierData:
            _, _, onTime, offTime = courierData[courier]
            if (onTime, offTime) not in courierGroups:
                courierGroups[(onTime, offTime)] = [[], offTime]
            courierGroups[(onTime, offTime)][0].append(courier)
else:
    for courier in courierData:
        courierGroups[courier] = [[courier], courierData[courier][3]]
globalOffTime = max(courierGroups[group][1] for group in courierGroups)





def TravelTime(loc1, loc2):
    x1, y1 = loc1[0], loc1[1]
    x2, y2 = loc2[0], loc2[1]
    return math.sqrt((x1-x2)**2 + (y1-y2)**2) / travelSpeed





for order in orderData:
    maxClickToDoorArrivalTime = orderData[order][2] + maxClickToDoor
    travelTime = (pickupServiceTime + dropoffServiceTime) / 2 + TravelTime(restaurantData[orderData[order][3]], orderData[order])
    orderData[order].append(maxClickToDoorArrivalTime - travelTime)
    orderData[order].append(maxClickToDoorArrivalTime)





def CompareOneIndex(op, dictionary, key1, key2, index):
    return op(dictionary[key1][index], dictionary[key2][index])





def CompareTwoIndices(op1, op2, dictionary, key1, key2, index1, index2):
    return CompareOneIndex(op1, dictionary, key1, key2, index1) and CompareOneIndex(op2, dictionary, key1, key2, index2)





def RemoveDominatedSequences(sequences):
    sequencesBySetAndLastOrder = defaultdict(list)
    for sequence in sequences:
        sequencesBySetAndLastOrder[(frozenset(sequence), sequence[-1])].append(sequence)
    sequencesBySetAndLastOrder = dict(sequencesBySetAndLastOrder)
    dominatedSequences = set()
    for group in sequencesBySetAndLastOrder:
        if len(sequencesBySetAndLastOrder[group]) > 1:
            for (sequence1, sequence2) in itertools.combinations(sequencesBySetAndLastOrder[group],2):
                if CompareTwoIndices(gt, lt, sequences, sequence1, sequence2, 2, 3):
                    dominatedSequences.add(sequence2)
                elif CompareTwoIndices(lt, gt, sequences, sequence1, sequence2, 2, 3):
                    dominatedSequences.add(sequence1)
    for sequence in dominatedSequences:
        del sequences[sequence]
    return sequences





# Calculate & dominate order sequences
for restaurant in restaurantData:
    sequenceLength = 1
    calculatedSequences = {}
    for order in ordersAtRestaurant[restaurant]:
        calculatedSequences[(order,)] = [restaurant, orderData[order][4], orderData[order][5], TravelTime(restaurantData[restaurant], orderData[order]) + (pickupServiceTime + dropoffServiceTime) / 2]
    for sequence in calculatedSequences:
        sequenceData[sequence] = calculatedSequences[sequence]
    if limitBundlesToSizeOne:
        continue
    while len(calculatedSequences) > 0:
        sequenceLength += 1
        newSequences = {}
        for sequence in calculatedSequences:
            for order in ordersAtRestaurant[restaurant]:
                if order not in sequence:
                    newSequence = sequence + (order,)
                    totalTravelTime = sequenceData[sequence][3] + dropoffServiceTime + TravelTime(orderData[sequence[-1]], orderData[order])
                    latestLeavingTime = min(sequenceData[sequence][2], orderData[order][6] - totalTravelTime)
                    earliestLeavingTime = max(sequenceData[sequence][1], orderData[order][4])
                    if earliestLeavingTime <= latestLeavingTime:
                        newSequences[newSequence] = [restaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime]
        if sequenceLength >= 3:
            newSequences = RemoveDominatedSequences(newSequences)
        calculatedSequences = newSequences
        for sequence in calculatedSequences:
            sequenceData[sequence] = calculatedSequences[sequence]
        if len(calculatedSequences) == 0:
            break





sequencesByRestaurantThenOrderSet = {}
for sequence in sequenceData:
    restaurant = sequenceData[sequence][0]
    if restaurant not in sequencesByRestaurantThenOrderSet:
        sequencesByRestaurantThenOrderSet[restaurant] = defaultdict(list)
    sequencesByRestaurantThenOrderSet[restaurant][frozenset(sequence)].append(sequence)
GiveMeAStatusUpdate('delivery sequences', sequenceData)





def CheckDominationPairs(sequenceToCheck, nextRestaurant):
    dominatedSequences = []
    for sequence in groupedPairs[(frozenset(sequenceToCheck), nextRestaurant)]:
        if sequence != sequenceToCheck:
            if CompareTwoIndices(lt, gt, sequenceNextRestaurantData, (sequenceToCheck, nextRestaurant), (sequence, nextRestaurant), 2, 3):
                return [sequenceToCheck]
            if CompareTwoIndices(gt, lt, sequenceNextRestaurantData, (sequenceToCheck, nextRestaurant), (sequence, nextRestaurant), 2, 3):
                dominatedSequences.append(sequence)
    return dominatedSequences





groupedPairs = defaultdict(list) # (frozenset(sequence), nextRestaurant): [sequence1, sequence2, sequence3, ...]
for sequence in sequenceData:
    finishTime = sequenceData[sequence][1] + sequenceData[sequence][3]
    for restaurant in restaurantData:
        arrivalAtRestaurant = finishTime + TravelTime(orderData[sequence[-1]], restaurantData[restaurant]) + (dropoffServiceTime + pickupServiceTime) / 2
        for order in ordersAtRestaurant[restaurant]:
            if order not in sequence:
                if orderData[order][5] > arrivalAtRestaurant:
                    travelTime = sequenceData[sequence][3] + TravelTime(orderData[sequence[-1]], restaurantData[restaurant]) + (dropoffServiceTime + pickupServiceTime) / 2
                    sequenceNextRestaurantData[(sequence, restaurant)] = sequenceData[sequence][:3] + [travelTime]
                    groupedPairs[(frozenset(sequence), restaurant)].append(sequence)
                    dominatedSequences = CheckDominationPairs(sequence, restaurant)
                    for dominatedSequence in dominatedSequences:
                        del sequenceNextRestaurantData[(dominatedSequence, restaurant)]
                        groupedPairs[(frozenset(sequence), restaurant)].remove(dominatedSequence)
                    break
groupedPairs = dict(groupedPairs)
GiveMeAStatusUpdate('post-domination pairs', sequenceNextRestaurantData)





untimedArcs = set()
# {((group1, 0), sequence1, nextRestaurant1), ((group2, 0), sequence2, nextRestaurant2), ...}
# Main untimedArcs
# Create (courierGroup, orderSequence, nextRestaurant) triples
# Loop through (orderSequence, nextRestaurant) pairs, and loop through groups, checking to see if valid together
# Valid if:
# 1. earliest leaving time is before the group's off time
# 2. courier can arrive at restaraunt before off time
# 3. courier can arrive at restaurant before latest leaving time
# 4. the arrival at the next restaurant is before the group's off time
# 5. there is at least one order at the next restaurant that is deliverable between the courier's arrival and the group's off time
# 6. the earliest leaving time plus the travel time is before the group's off time (less refined version of 4)
# The courier must leave in time to deliver its orders, as well as in time to
# deliver an order at the next restaurant.
for sequence, nextRestaurant in sequenceNextRestaurantData:
    restaurant, earliestLeavingTime, latestLeavingTime, travelTime = sequenceNextRestaurantData[sequence, nextRestaurant]
    for group in courierGroups:
        offTime = courierGroups[group][1]
        if offTime >= earliestLeavingTime + travelTime: # check conditions 1, 6
            foundValidCourier = False
            bestArrivalTime = globalOffTime
            for courier in courierGroups[group][0]:
                commute = TravelTime(courierData[courier], restaurantData[restaurant]) + pickupServiceTime / 2
                arrivalAtDepartureRestaurant = courierData[courier][2] + commute
                if arrivalAtDepartureRestaurant <= min(latestLeavingTime, offTime): # check conditions 2 and 3
                    foundValidCourier = True
                    if arrivalAtDepartureRestaurant < bestArrivalTime:
                        bestArrivalTime = arrivalAtDepartureRestaurant
            if foundValidCourier:
                earliestDepartureFromDepartureRestaurant = max(bestArrivalTime, earliestLeavingTime) # can't leave before arrive
                if earliestDepartureFromDepartureRestaurant > latestLeavingTime:
                    print('Main untimed arc error 1!', str(group), str(sequence), str(nextRestaurant))
                arrivalAtNextRestaurant = earliestDepartureFromDepartureRestaurant + travelTime
                if arrivalAtNextRestaurant <= offTime: # check condition 4
                    foundValidOrder = False
                    bestOrderLatestLeavingTime = 0
                    for order in ordersAtRestaurant[nextRestaurant]:
                        if order not in sequence:
                            if orderData[order][4] <= offTime and orderData[order][5] >= arrivalAtNextRestaurant:
                                foundValidOrder = True
                                if orderData[order][5] > bestOrderLatestLeavingTime:
                                    bestOrderLatestLeavingTime = orderData[order][5]
                    if foundValidOrder: # check condition 5
                        latestArrivalAtNextRestaurant = min(bestOrderLatestLeavingTime, offTime)
                        latestDepartureAtDepartureRestaurant = min(latestArrivalAtNextRestaurant - travelTime, latestLeavingTime)
                        if latestDepartureAtDepartureRestaurant < earliestDepartureFromDepartureRestaurant:
                            print('Main untimed arc error 2!', str(group), str(sequence), str(nextRestaurant))
                        untimedArcs.add(((group, 0), sequence, nextRestaurant))
                        untimedArcData[((group, 0), sequence, nextRestaurant)] = [restaurant, earliestDepartureFromDepartureRestaurant, latestDepartureAtDepartureRestaurant, travelTime]
GiveMeAStatusUpdate('main untimedArcs', untimedArcs)





# Exit untimedArcs
# Create sequence-courier (off time) pairs, with nextRestaurant = 0
# An untimed exit arc is of the form ((group,), sequence, 0)
# Iterate through all group, sequence pairs, checking if compatible:
# - Earliest leaving time must be before the group's off time
# - At least one courier can arrive at the restaurant before off time
# - Out of those couriers, at least one must arrive before latest leaving time
exitUntimedArcsByCourierRestaurant = defaultdict(list)
for sequence in sequenceData:
    restaurant, earliestLeavingTime, latestLeavingTime, totalTravelTime = sequenceData[sequence]
    for group in courierGroups:
        offTime = courierGroups[group][1]
        if offTime >= earliestLeavingTime: # sequence must be deliverable in courier's shift
            foundValidCourier = False
            bestArrivalTime = globalOffTime
            for courier in courierGroups[group][0]:
                commute = TravelTime(courierData[courier], restaurantData[restaurant]) + pickupServiceTime / 2
                arrivalTime = courierData[courier][2] + commute
                if arrivalTime <= min(offTime, latestLeavingTime): # courier must arrive at restaurant in-shift, and in time to pick up and deliver order
                    foundValidCourier = True
                    bestArrivalTime = min(arrivalTime, bestArrivalTime)
            if foundValidCourier: # only add arc if valid courier found, add data for best courier found
                untimedArcs.add(((group, 0), sequence, 0))
                untimedArcData[((group, 0), sequence, 0)] = [restaurant, max(earliestLeavingTime, bestArrivalTime), min(latestLeavingTime, offTime), totalTravelTime]
                exitUntimedArcsByCourierRestaurant[(group, restaurant)].append(((group, 0), sequence, 0))
exitUntimedArcsByCourierRestaurant = dict(exitUntimedArcsByCourierRestaurant)
GiveMeAStatusUpdate('main + exit untimedArcs', untimedArcs)

# Entry untimed arcs
# An entry untimed arc is of the form ((courierGroup, courier), (), restaurant)
# Iterate through couriers within courier groups and restaurants, finding compatible pairs
# Compatible if:
# - The courier can arrive at the restaurant before offtime
# - There is at least one order at the restaurant such that:
#   - The order's ready time is before the courier's off time
#   - The order's latest departure time is after the courier's arrival time
# Assume for calculations that the courier will travel directly to the restaurant, from home, at the beginning of the shift

for group in courierGroups:
    offTime = courierGroups[group][1]
    for courier in courierGroups[group][0]:
        courierShiftStartTime = courierData[courier][2]
        for restaurant in restaurantData:
            # Looping through every courier-restaurant pair
            commuteToRestaurant = TravelTime(courierData[courier], restaurantData[restaurant]) + pickupServiceTime / 2
            earliestArrivalAtRestaurant = courierShiftStartTime + commuteToRestaurant
            if earliestArrivalAtRestaurant <= offTime:
                # Checking that the courier can arrive before its off time
                latestAllowedCourierArrival = 0
                for order in ordersAtRestaurant[restaurant]:
                    # Loop through orders, to check if courier-restaurant pair is valid
                    if orderData[order][4] <= offTime and orderData[order][5] >= earliestArrivalAtRestaurant:
                        # This order is deliverable by the courier
                        if orderData[order][5] > offTime:
                            # If this is true, the courier has no time restriction on when it arrives at the restaurant
                            latestAllowedCourierArrival = offTime
                            break
                        latestAllowedCourierArrival = max(latestAllowedCourierArrival, orderData[order][5])
                if latestAllowedCourierArrival >= earliestArrivalAtRestaurant:
                    if earliestArrivalAtRestaurant <= 0:
                        print('Error! Courier arriving at restaurant before the day starts!', courier, restaurant)
                    # If this is true, then there must have been at least one valid order to bring the latest allowed arrival above zero
                    untimedArcs.add(((group, courier), (), restaurant))
                    untimedArcData[((group, courier), (), restaurant)] = [0, courierShiftStartTime, latestAllowedCourierArrival - commuteToRestaurant, commuteToRestaurant]
GiveMeAStatusUpdate('untimed arcs total', untimedArcs)

untimedArcsByCourierRestaurant = defaultdict(list)
untimedArcsByCourierNextRestaurant = defaultdict(list)
for arc in untimedArcs:
    if arc[1] == ():
        untimedArcsByCourierRestaurant[(arc[0][0], 0)].append(arc)
    else:
        untimedArcsByCourierRestaurant[(arc[0][0], untimedArcData[arc][0])].append(arc)
    untimedArcsByCourierNextRestaurant[(arc[0][0], arc[2])].append(arc)
untimedArcsByCourierRestaurant = dict(untimedArcsByCourierRestaurant)
untimedArcsByCourierNextRestaurant = dict(untimedArcsByCourierNextRestaurant)





nodesInModel = set()
# A node is a (courierGroup, restaurant, time) triple. If globalNodeIntervals
# is set to True, then node times will be integer multiples of the 
# nodeTimeInterval. Also, there is a node at restaurant = 0, time = 0 and
# restaurant = 0, time = globalOffTime for every courier group.
# The first interesting time per (courierGroup, restaurant) pair is the later
# of when a courier can first get to the restaurant, and when the first order
# is ready. The last interesting time per pair is the earlier of the group's
# off time, and when the last order must have left the restaurant by.
nodeTimesByCourierRestaurant = defaultdict(list)
for group, restaurant in untimedArcsByCourierRestaurant:
    if restaurant != 0:
        offTime = courierGroups[group][1]
        
        # Calculate the first time that we should consider, i.e., the time for the first node for that group-restaurant pair
        earliestArrivalTime = min(untimedArcData[arc][1] + untimedArcData[arc][3] for arc in untimedArcsByCourierNextRestaurant[(group, restaurant)])
        earliestOrderTime = min(orderData[o][4] for o in ordersAtRestaurant[restaurant] if orderData[o][4] <= offTime if orderData[o][5] >= earliestArrivalTime)
        firstInterestingTime = max(earliestArrivalTime, earliestOrderTime)
        
        # Calculate the last time that we should consider, i.e., the time for the last node for that group-restaurant pair
        groupOffTime = courierGroups[group][1]
        latestOrderTime = max(orderData[o][5] for o in ordersAtRestaurant[restaurant] if orderData[o][4] <= offTime if orderData[o][5] >= earliestArrivalTime)
        lastInterestingTime = min(offTime, latestOrderTime)
        
        # If globalNodeIntervals is true, then all node times will be integer multiples of the nodeTimeInterval
        if globalNodeIntervals:
            possibleNodeTimes = list(i for i in range(0, globalOffTime + 1, nodeTimeInterval))
            firstNodeTime = max(t for t in possibleNodeTimes if t <= firstInterestingTime)
        else:
            firstNodeTime = firstInterestingTime
        
        # All node times, when compared to other node times for the same group-restaurant pair, differ by an integer multiple of the nodeTimeInterval
        # In addition, the node times are every time that fulfills the above condition and is less than or equal to the lastInterestingTime
        nodeTime = firstNodeTime
        while nodeTime <= lastInterestingTime:
            nodesInModel.add((group, restaurant, nodeTime))
            nodeTimesByCourierRestaurant[(group, restaurant)].append(nodeTime)
            nodeTime += nodeTimeInterval

# In addition to having nodes for every group-restaurant pair, we need a starting node and an ending node for the couriers at 'home', or restaurant 0
for group in courierGroups:
    nodesInModel.add((group, 0, 0))
    nodesInModel.add((group, 0, globalOffTime))
    nodeTimesByCourierRestaurant[(group, 0)] = [0, globalOffTime]
nodeTimesByCourierRestaurant = dict(nodeTimesByCourierRestaurant)
GiveMeAStatusUpdate('nodes generated', nodesInModel)

nodesByOfftimeRestaurantPair = defaultdict(list)
# (offTime, departureRestaurant): [(offTime, departureRestaurant, time1), (offTime, departureRestaurant, time2), ...]
for node in nodesInModel:
    nodesByOfftimeRestaurantPair[node[:2]].append(node)
nodesByOfftimeRestaurantPair = dict(nodesByOfftimeRestaurantPair)

timedArcs = set()
# A timed arc is a sextuple of the form ((g, c), r1, t1, s, r2, t2), where:
# - g is the courier-group that is following the arc
# - c != 0 if the arc is an entry arc, otherwise, c = 0. c is the courier that completes the arc, c = 0 means, at least theoretically, any of multiple couriers can do it
# - r1 is the departure restaurant. If the arc is not a waiting arc, then r1 is determined by s
# - t1 is the time of the departure node
# - s is the sequence that is delivered on the journey between the two nodes
# - r2 is the arrival restaurant
# - t2 is the time of the arrival node. t2 is determined by the untimed arc ((g,c),s,r2) and the time t1
# A waiting arc is a timed arc such that r1 = r2 and s = (). Multiple couriers can follow the one timed arc in the one solution
# Generation of timed arcs:
# - Loop through every untimed arc, that is, ((g,c),s,r2)
# - Loop through every possible starting node, and calculate the corresponding ending node
# - Dominate the timed arcs
# Two special cases of untimed arcs will be dealt with separately:
# - s = (). In this case, the untimed arc is an entry arc, and the timed arc will only have one possible starting node (that is, home) and thus one corresponding ending node
# - r2 = 0. In this case, the untimed arc is an exit arc, and the timed arc will only have one possible ending node (that is, home) and thus one corresponding starting node
# Waiting arcs will be generated separately
for ((g, c), s, r2) in untimedArcData:
    r1, earliestDepartureTime, latestDepartureTime, travelTime = untimedArcData[((g,c), s, r2)]
    if s == ():
        # untimed arc is an entry arc. The timed arc starts at home, and goes to the first possible node
        arrivalTimeAtRestaurant = untimedArcData[((g,c),s,r2)][1] + untimedArcData[((g,c),s,r2)][3]
        if min(nodeTimesByCourierRestaurant[(g,r2)]) > arrivalTimeAtRestaurant:
            arrivalNodeTime = min(nodeTimesByCourierRestaurant[(g,r2)])
        else:
            arrivalNodeTime = max(t for t in nodeTimesByCourierRestaurant[(g,r2)] if t <= arrivalTimeAtRestaurant)
        timedArcs.add(((g,c), 0, 0, (), r2, arrivalNodeTime))
    
    elif r2 == 0:
        # untimed arc is an exit arc. The timed arc ends at home, and comes from the last possible node
        departureNodeTime = max(t for t in nodeTimesByCourierRestaurant[(g,r1)] if t <= latestDepartureTime)
        timedArcs.add(((g,c), r1, departureNodeTime, s, r2, globalOffTime))
    
    else:
        # untimed arc is a main arc, going from restaurant to restaurant while delivering a sequence of orders        
        offTime = courierGroups[g][1]
        nodeTimesAtLeavingRestaurant = nodeTimesByCourierRestaurant[(g, r1)]
        nodeTimesAtArrivingRestaurant = nodeTimesByCourierRestaurant[(g, r2)]
        nodeTimesAtLeavingRestaurant.sort()
        nodeTimesAtArrivingRestaurant.sort()
        
        # find the first arc's leaving time - the largest node time that is before the earliest leaving time
        if min(nodeTimesAtLeavingRestaurant) <= earliestDepartureTime:
            firstArcLeavingTime = max(i for i in nodeTimesAtLeavingRestaurant if i <= earliestDepartureTime)
        else:
            print('Error: No early enough node time for arc conversion to timed arc!', ((g, c), s, r2))
            if min(nodeTimesAtLeavingRestaurant) > latestDepartureTime:
                break
            else:
                firstArcLeavingTime = min(nodeTimesAtLeavingRestaurant)
        
        # Add a timed arc for every departing node time valid for the untimed arc
        # Start times increase by the nodeTimeInterval parameter
        currentNodeTime = firstArcLeavingTime
        timedArcsToAdd = []
        while currentNodeTime <= latestDepartureTime:
            arrivalAtNextRestaurant = max(currentNodeTime, earliestLeavingTime) + travelTime
            # Two cases: there are nodes at the arriving restaurant around when the courier arrives, or not
            if min(nodeTimesAtArrivingRestaurant) <= arrivalAtNextRestaurant:
                # Arrival node time is given by the latest node time at the restaurant, that is before the arrival time
                arrivalNodeTime = max(i for i in nodeTimesAtArrivingRestaurant if i <= arrivalAtNextRestaurant)
            else:
                # Arrival node time is the earliest node time at the restaurant, that is after the arrival time
                arrivalNodeTime = min(nodeTimesAtArrivingRestaurant)
            if arrivalNodeTime < currentNodeTime:
                print('Error: timed arc going backwards in time!', ((g,c),s,r2), currentNodeTime)
                break
            timedArcsToAdd.append(((g,c), r1, currentNodeTime, s, r2, arrivalNodeTime))
            currentNodeTime += nodeTimeInterval
        
        # Dominate the timed arcs
        # We know all newly generated timed arcs have same courier group, departure restaurant, sequence and arrival restaurant
        # We also know there is a maximum of one timed arc for any departure time
        # timedArc1 dominates timedArc2 if they have the same arrival node time, but timedArc1 has a later leaving node time
        dominatedArcs = []
        for timedArc1, timedArc2 in itertools.combinations(timedArcsToAdd, 2):
            # iterate through all pairs of timed arcs that were just calculated
            if timedArc1[5] == timedArc2[5]:
                # check if they have the same arrival node time
                if timedArc1[2] < timedArc2[2]:
                    # timedArc1 has an earlier leaving node time
                    dominatedArcs.append(timedArc1)
                elif timedArc1[2] > timedArc2[2]:
                    # timedArc2 has an earlier leaving node time
                    dominatedArcs.append(timedArc2)
        
        # Add all the newly generated timed arcs, ignoring those that were dominated
        for timedArc in timedArcsToAdd:
            if timedArc not in dominatedArcs:
                timedArcs.add(timedArc)
    
# Waiting arcs
def NodeTime(node):
    return node[2]
for pair in nodesByOfftimeRestaurantPair:
    nodeList = nodesByOfftimeRestaurantPair[pair]
    if len(nodeList) > 0:
        nodeList.sort(key = NodeTime)
        for i in range(1, len(nodeList)):
            timedArcs.add(((pair[0],0), pair[1], nodeList[i-1][2], (), pair[1], nodeList[i][2]))
GiveMeAStatusUpdate('timed arcs', timedArcs)





arcsByDepartureNode = defaultdict(list) # (g,r1,t1): [timedArc1, timedArc2, ...]
arcsByArrivalNode = defaultdict(list) # (g,r2,t2): [timedArc1, timedArc2, ...]
arcsByCourier = defaultdict(list) # g: [timedArc1, timedArc2, ...]
arcsByOrder = {o: [] for o in orderData}
outArcsByCourier = {c: [] for c in courierData}
departureArcsByCourierAndRestaurant = defaultdict(list) # (g,r1): [timedArc1, timedArc2, ...]
arrivalArcsByCourierAndRestaurant = defaultdict(list) # (g,r2): [timedArc1, timedArc2, ...]
arcsByUntimedArc = {u: [] for u in untimedArcData}
waitingArcsByGroupRestaurant = defaultdict(list)

for arc in timedArcs:
    ((g,c),r1,t1,s,r2,t2) = arc
    arcsByDepartureNode[g,r1,t1].append(arc)
    arcsByArrivalNode[g,r2,t2].append(arc)
    arcsByCourier[g].append(arc)
    departureArcsByCourierAndRestaurant[g,r1].append(arc)
    arrivalArcsByCourierAndRestaurant[g,r2].append(arc)
    for o in s:
        arcsByOrder[o].append(arc)
    if r1 == 0 and r2 != 0:
        outArcsByCourier[c].append(arc)
    if r1 != r2 or s != ():
        arcsByUntimedArc[(g,c),s,r2].append(arc)
    if r1 == r2 and s == ():
        waitingArcsByGroupRestaurant[g,r1].append(arc)

arcsByDepartureNode = dict(arcsByDepartureNode)
arcsByArrivalNode = dict(arcsByArrivalNode)
arcsByCourier = dict(arcsByCourier)
departureArcsByCourierAndRestaurant = dict(departureArcsByCourierAndRestaurant)
arrivalArcsByCourierAndRestaurant = dict(arrivalArcsByCourierAndRestaurant)
waitingArcsByGroupRestaurant = dict(waitingArcsByGroupRestaurant)

for order in arcsByOrder:
    if len(arcsByOrder[order]) == 0:
        print('Error: No timed arcs deliver order ' + str(order) + '!')
for courier in outArcsByCourier:
    if len(outArcsByCourier[courier]) == 0:
        print('Error: Courier ' + str(courier) + ' has no entry arcs!')
for untimedArc in arcsByUntimedArc:
    if len(arcsByUntimedArc[untimedArc]) == 0:
        print('Error: Untimed arc ' + str(untimedArc) + ' has no matching timed arcs!')





print()
m = Model('MDRP')





arcs = {arc: m.addVar() for arc in timedArcs if arc[2] <= arc[5]}
doesThisCourierStart = {c: m.addVar() for c in courierData}
# payments = {group: m.addVar() for group in courierGroups}





# m.setObjective(quicksum(payments[g] for g in courierGroups))





flowConstraint = {node: m.addConstr(quicksum(arcs[arc] for arc in arcsByDepartureNode[node]) == quicksum(arcs[arc] for arc in arcsByArrivalNode[node])) for node in nodesInModel if node[1] != 0}
outArcsIffLeaveHome = {c: m.addConstr(quicksum(arcs[arc] for arc in outArcsByCourier[c]) == doesThisCourierStart[c]) for c in courierData}
deliverOrders = {o: m.addConstr(quicksum(arcs[arc] for arc in arcsByOrder[o]) == 1) for o in orderData}
# paidPerDelivery = {g: m.addConstr(payments[g] >= quicksum(arcs[arc] * len(arc[3]) * payPerDelivery for arc in arcsByCourier[g]) + quicksum((courierData[c][3] - courierData[c][2]) * minPayPerHour / 60 * (1-doesThisCourierStart[c]) for c in courierGroups[g][0])) for g in courierGroups}
# paidPerTime = {g: m.addConstr(payments[g] >= quicksum((courierData[courier][3] - courierData[courier][2]) * minPayPerHour / 60 for courier in courierGroups[g][0])) for g in courierGroups}
print('Completed main constraints, time = ' + str(time() - programStartTime))
print()





if addValidInequalityConstraints:
    if not addVIRecursively:
        print('Adding all VI constraints')
        # Code for doing all VIs:
        VIConstraints = {}
        for arc in untimedArcs:
            if arc[1] != (): # not an entry arc, do predecessor valid inequalities
                validPredecessorUntimedArcs = []
                leavingRestaurant, _, latestLeavingTime, _ = untimedArcData[arc]
                for untimedArc in untimedArcsByCourierNextRestaurant[(arc[0][0], leavingRestaurant)]:
                    if untimedArcData[untimedArc][1] + untimedArcData[untimedArc][3] <= latestLeavingTime:
                        if set(arc[1]) & set(untimedArc[1]) != set():
                            continue
                        validPredecessorUntimedArcs.append(untimedArc)
                if len(validPredecessorUntimedArcs) == 0:
                    print('No predecessor arcs', arc)
                VIConstraints[(-1,arc,tuple(validPredecessorUntimedArcs))] = m.addConstr(quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[arc])
                            <= quicksum(arcs[timedArc] for untimedArc in validPredecessorUntimedArcs for timedArc in arcsByUntimedArc[untimedArc]))
            if arc[2] != 0: # not an exit arc, do successor valid inequalities
                validSuccessorUntimedArcs = []
                _, earliestLeavingTime, _, travelTime = untimedArcData[arc]
                for untimedArc in untimedArcsByCourierRestaurant[(arc[0][0], arc[2])]:
                    if untimedArcData[untimedArc][2] >= earliestLeavingTime + travelTime:
                        if set(arc[1]) & set(untimedArc[1]) != set():
                            continue
                        validSuccessorUntimedArcs.append(untimedArc)
                if len(validSuccessorUntimedArcs) == 0:
                    print('No successor arcs', arc)
                VIConstraints[(1,arc,tuple(validSuccessorUntimedArcs))] = m.addConstr(quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[arc])
                            <= quicksum(arcs[timedArc] for untimedArc in validSuccessorUntimedArcs for timedArc in arcsByUntimedArc[untimedArc]))
        GiveMeAStatusUpdate('VI Constraints', VIConstraints)
        m.optimize()
    
    else:
        # Code for removing broken VIs:
        m.setParam('OutputFlag', 0)
        extraConstraints = {}
        constraintDict = {}
        t = 0
        print('# of arcs, # VI added, total VI count, time')
        while True:
            constraintsAdded = 0
            m.optimize()
            usedUntimedArcs = [] # (courierGroup, orderSequence, r2)
            for arc in arcs:
                if arcs[arc].x > 0.001: # arc was turned on
                    if arc[1] != arc[4] or arc[3] != (): # not a waiting arc
                        untimedArc = (arc[0], arc[3], arc[4])
                        usedUntimedArcs.append(untimedArc)
            # eventually move the following into a function to go after the generation of 'usedUntimedArcs'?
            for arc in usedUntimedArcs: # (group, orderSequence, r2)
                activationOfUntimedArc = sum(arcs[timedArc].x for timedArc in arcsByUntimedArc[arc])
                if arc[1] != (): # not an entry arc, do predecessor valid inequalities
                    validPredecessorUntimedArcs = []
                    leavingRestaurant, _, latestLeavingTime, _ = untimedArcData[arc]
                    for untimedArc in untimedArcsByCourierNextRestaurant[(arc[0][0], leavingRestaurant)]:
                        if untimedArcData[untimedArc][1] + untimedArcData[untimedArc][3] <= latestLeavingTime:
                            if set(arc[1]) & set(untimedArc[1]) != set():
                                continue
                            validPredecessorUntimedArcs.append(untimedArc)
                    if len(validPredecessorUntimedArcs) == 0:
                        print('No predecessor arcs', arc)
                    activationOfPredecessors = sum(arcs[timedArc].x for untimedArc in validPredecessorUntimedArcs for timedArc in arcsByUntimedArc[untimedArc])
                    if activationOfUntimedArc > activationOfPredecessors + 0.01:
                        constraintDict[t] = m.addConstr(quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[arc])
                                    <= quicksum(arcs[timedArc] for untimedArc in validPredecessorUntimedArcs for timedArc in arcsByUntimedArc[untimedArc]))
                        extraConstraints[t] = [1, arc, validPredecessorUntimedArcs, activationOfUntimedArc - activationOfPredecessors]
                        constraintsAdded += 1
                        t += 1
                if arc[2] != 0: # not an exit arc, do successor valid inequalities
                    validSuccessorUntimedArcs = []
                    _, earliestLeavingTime, _, travelTime = untimedArcData[arc]
                    for untimedArc in untimedArcsByCourierRestaurant[(arc[0][0], arc[2])]:
                        if untimedArcData[untimedArc][2] >= earliestLeavingTime + travelTime:
                            if set(arc[1]) & set(untimedArc[1]) != set():
                                continue
                            validSuccessorUntimedArcs.append(untimedArc)
                    if len(validSuccessorUntimedArcs) == 0:
                        print('No successor arcs', arc)
                    activationOfSuccessors = sum(arcs[timedArc].x for untimedArc in validSuccessorUntimedArcs for timedArc in arcsByUntimedArc[untimedArc])
                    if activationOfUntimedArc > activationOfSuccessors + 0.01:
                        constraintDict[t] = m.addConstr(quicksum(arcs[timedArc] for timedArc in arcsByUntimedArc[arc])
                                    <= quicksum(arcs[timedArc] for untimedArc in validSuccessorUntimedArcs for timedArc in arcsByUntimedArc[untimedArc]))
                        extraConstraints[t] = [2, arc, validSuccessorUntimedArcs, activationOfUntimedArc - activationOfSuccessors]
                        constraintsAdded += 1
                        t += 1
            
            # Output
            # Number of arcs used, number of VI constraints added, total number of VI constraints, time
            print(len(usedUntimedArcs), '   ', constraintsAdded, '   ', t, '   ', int(time() - programStartTime))
            if constraintsAdded == 0:
                break
print()
print('Time = ' + str(time() - programStartTime))




callbackCuts = []
def ComputeAndRemoveMinimalIllegalNetwork(listOfTimedArcs):
    # Take the list of timed arcs, and convert them to untimed arcs
    usedUntimedArcs = []
    for ((g,c), _, _, s, r2, _) in listOfTimedArcs:
        untimedArc = ((g,c), s, r2)
        if untimedArc in usedUntimedArcs:
            print('Error! Duplicate use of untimed arc in solution!', untimedArc)
        usedUntimedArcs.append(untimedArc)
    
    # Find all possible predecessor-successor pairs
    successorsForArc = defaultdict(list)
    predecessorsForArc = defaultdict(list)
    for (arc1, arc2) in itertools.combinations(usedUntimedArcs, 2):
        arc1Data = untimedArcData[arc1]
        arc2Data = untimedArcData[arc2]
        if arc1Data[1] + arc1Data[3] <= arc2Data[2] and arc1[2] == arc2Data[0] and arc1[2] != 0:
            # Earliest arrival before latest departure
            # The arrival location of the first arc is the departure location of the second
            # The first arc does not head home
            successorsForArc[arc1].append(arc2)
            predecessorsForArc[arc2].append(arc1)
        if arc2Data[1] + arc2Data[3] <= arc1Data[2] and arc2[2] == arc1Data[0] and arc2[2] != 0:
            successorsForArc[arc2].append(arc1)
            predecessorsForArc[arc1].append(arc2)
    successorsForArc = dict(successorsForArc)
    predecessorsForArc = dict(predecessorsForArc)
    
    # Create a new model
    IPD = Model('Illegal Path Determination')
    X = {(arc, successor): IPD.addVar(vtype=GRB.BINARY) for arc in successorsForArc for successor in successorsForArc[arc]}
    T = {arc: IPD.addVar() for arc in usedUntimedArcs}
    
    leaveAfterEarlyTime = {arc: IPD.addConstr(T[arc] >= untimedArcData[arc][1]) for arc in usedUntimedArcs}
    leaveBeforeLateTime = {arc: IPD.addConstr(T[arc] <= untimedArcData[arc][2]) for arc in usedUntimedArcs}
    enoughTimeForBothArcs = {(i,j): IPD.addConstr(T[i]+untimedArcData[i][3] <= T[j] + 
                                  (untimedArcData[i][2]+untimedArcData[i][3]-untimedArcData[j][1])*(1-X[i,j]))
                              for (i,j) in X}
    predecessorArcsUsedOnce = {i: IPD.addConstr(quicksum(X[i,j] for j in successorsForArc[i]) == 1) for i in successorsForArc}
    successorArcsUsedOnce = {j: IPD.addConstr(quicksum(X[i,j] for i in predecessorsForArc[j]) == 1) for j in predecessorsForArc}
    
    # Solve the model
    IPD.setParam('OutputFlag', 0)
    IPD.optimize()
    
    # Compute IIS
    if IPD.Status == GRB.INFEASIBLE:
        IPD.computeIIS()
    
        # Compute Invalid Network
        invalidUntimedArcs = set()
        for arc in usedUntimedArcs:
            if leaveAfterEarlyTime[arc].IISConstr or leaveBeforeLateTime[arc].IISConstr:
                invalidUntimedArcs.add(arc)
        for predecessor, successor in X:
            if enoughTimeForBothArcs[predecessor, successor].IISConstr:
                invalidUntimedArcs.add(predecessor)
                invalidUntimedArcs.add(successor)
            else:
                if predecessorArcsUsedOnce[predecessor].IISConstr:
                    invalidUntimedArcs.add(predecessor)
                if successorArcsUsedOnce[successor].IISConstr:
                    invalidUntimedArcs.add(successor)
        
        # Find possible replacement arcs
        alternatePredecessorArcs = set()
        alternateSuccessorArcs = set()
        for arc in invalidUntimedArcs:
            (group, _), _, arrivalRestaurant = arc
            departureRestaurant, earliestLeavingTime, latestLeavingTime, travelTime = untimedArcData[arc]
            for untimedArc in untimedArcsByCourierNextRestaurant[group, departureRestaurant]:
                if untimedArc not in usedUntimedArcs:
                    # Finding predecessors. A valid predecessor will have earliest
                    # arrival time before the arc has to leave
                    earliestArrival = untimedArcData[untimedArc][1] + untimedArcData[untimedArc][3]
                    if earliestArrival <= latestLeavingTime:
                        alternatePredecessorArcs.add(untimedArc)
            
            for untimedArc in untimedArcsByCourierRestaurant[group, arrivalRestaurant]:
                if untimedArc not in usedUntimedArcs:
                    # Finding successors. A valid successor will have latest leaving
                    # time after the arc's earliest arrival
                    earliestArrival = earliestLeavingTime + travelTime
                    if earliestArrival <= untimedArcData[untimedArc][2]:
                        alternateSuccessorArcs.add(untimedArc)
        
        # Remove Invalid Network
        m.cbLazy(quicksum(arcs[timedArc] for untimedArc in invalidUntimedArcs for timedArc in arcsByUntimedArc[untimedArc])
                  <= len(invalidUntimedArcs) - 1 + quicksum(arcs[timedArc] for untimedArc in alternatePredecessorArcs for timedArc in arcsByUntimedArc[untimedArc]))
        m.cbLazy(quicksum(arcs[timedArc] for untimedArc in invalidUntimedArcs for timedArc in arcsByUntimedArc[untimedArc])
                  <= len(invalidUntimedArcs) - 1 + quicksum(arcs[timedArc] for untimedArc in alternateSuccessorArcs for timedArc in arcsByUntimedArc[untimedArc]))
        callbackCuts.append((-1, invalidUntimedArcs, alternatePredecessorArcs))
        callbackCuts.append((1, invalidUntimedArcs, alternateSuccessorArcs))

def Callback(model, where):
    if where == GRB.Callback.MIPSOL:
        timedArcValues = {arc: value for (arc, value) in zip(arcs.keys(), model.cbGetSolution(list(arcs.values())))}
        usedTimedArcs = {arc: timedArcValues[arc] for arc in timedArcValues if timedArcValues[arc] > 0.01}
        usedArcsByGroup = {group: [] for group in courierGroups}
        for arc in usedTimedArcs:
            if arc[3] != () or arc[1] != arc[4]:
                usedArcsByGroup[arc[0][0]].append(arc)
        for group in usedArcsByGroup:
            ComputeAndRemoveMinimalIllegalNetwork(usedArcsByGroup[group])

for arc in arcs:
    if arc[1] != arc[4] or arc[3] != ():
        arcs[arc].vtype=GRB.BINARY

for courier in doesThisCourierStart:
    doesThisCourierStart[courier].vtype=GRB.BINARY

m.setParam('Method', 2)
m.setParam('LazyConstraints', 1)
m.setParam('OutputFlag', 1)
m.optimize(Callback)

print('Time = ' + str(time() - programStartTime))
