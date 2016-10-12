#!/usr/bin/env python

###############################################################################################
###############################################################################################
###############################################################################################

# SEAC - Source Extraction Algoirthm for COBRaS
# Jack Morford - 121016
# Based on original fluxextractor script by Luke Peck (19/09/2013)

### A source extraction script written in parseltongue for the interaction with images within
# AIPS. This can be run on any image that is stored within AIPS. Set the seed and flood
# threshold levels to determine the level down to which a source shall be searched for...
# The program can return images of each extracted source along with a textfile containing
# the positions, max pixel flux, integrated flux and associated errors. 

###############################################################################################
###############################################################################################
###############################################################################################
### Import modules ############################################################################


from AIPS import AIPS, AIPSDisk
from AIPSTask import AIPSTask, AIPSList
from AIPSData import AIPSUVData, AIPSImage, AIPSCat

from AIPSTV import AIPSTV
import Wizardry.AIPSData
from Wizardry.AIPSData import AIPSUVData as WAIPSUVData
from Wizardry.AIPSData import AIPSImage as WAIPSImage

import LocalProxy
from xmlrpclib import ServerProxy

import copy, optparse, os, sys
import re, string
import os.path

import inspect
import warnings
warnings.defaultaction = "always"

import collections
import numpy
import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages
from matplotlib.pyplot import figure, close, savefig, rcParams, cm, cla, clf, text
import numpy as np
import scipy
from scipy import stats
from scipy import signal
import platform
import cPickle as pickle

import math, time, datetime
from time import gmtime, strftime, localtime
ti = time.time()

###############################################################################################
###############################################################################################
###############################################################################################
### User inputs ###############################################################################

AIPS.userno = 1
filename = 'ANIMAGE'
fileclass = 'IM'    # class of image
fileseq = 1
filedisk = 1

outname = 'NAMEME' # The program will create a directory within the path2folder directory labelled outname
                    # If running on the same image multiple times I'd suggest you alter this ti aviod overwriting
                    # previous outputs from SEAC

path2folder = '/user/home/'

write_2_file = 'yes'    # write the outputs to a source list.

noise_from_local_background = 'yes'    # get local noise from annulus around sources only if fluxes_from_jmfit = 'no'

fluxes_from_jmfit = 'no'    # yes = get fluxes and positions from jmfit, no = flux extractor

faint_detection = 'no'    # if yes looks for sources < 5 SNR as well as higher (may take longer to run)

beampercentage = 1.   # In fracitonal form, select the percentage of the beam size that each island must
                        # be larger than to be declared as a source. Default = 1

create_mask_of_detection = 'no' # if yes need a copy of the image with the klass as maskclass below.

rms_arcsecond_radius = 2. # if noise_from_local_background == 'yes', this sets the radius of a box around the
                            # source from which the local rms will be calculated.

plotarray = 'yes'   # choose this option to plot the detected sources along with the area covered by the algorithm

usenoisemap = 'yes' # if yes, a noise map will be calculated and the seed-threshold will be told to vary across
                    # the image - a good idea if you have a wide field image where the noise varies a lot over it!

noisemapres = 4  # choose the resoltuion of the calculated noise map...(i.e. if 8, there will be 8x8 separate noise
                  # estimates across the image...) this depends on the size of your image and the cellsize (i.e. the
                  # area on the sky that one pixel represents)

findweightedcorrds = 'yes' # this calcualtes the position of each source by weighting the pixels accordingly...

sigma_S = 5.0 # seed_threshold - first finds indiviudal pixels above a certain level
sigma_F = 3.0 # flood_threshold - then tests adjacent pixels to seed pixels to see if they're above this (flood) level




################################################################################################
################################################################################################
################################################################################################
### Defintions #################################################################################


# Create a list of sources with weighted positions, max pixel positions, integrated flux with errors and max pixel flux...
def create_source_list(weighted_positions, max_pixel_positions, fluxes, flux_errors, snr_sources, island_max, image_rms_dic, path2folder, filename, fileclass, fileseq):

    textfile_name = path2folder + filename + '_' + fileclass + '_' + str(fileseq) + '.fx'
    text_file = open(textfile_name, 'w')

    # NOTE: each index of the list that goes into creating the textfile...
    # index 0 = weighted_ra_degrees
    # index 1 = weighted_ra_degrees_error
    # index 2 = weighted_dec_degrees
    # index 3 = weighted_dec_degrees_error
    # index 4 = max_pixel_ra_degrees
    # index 5 = max_pixel_dec_degrees
    # index 6 = max_pixel_ra_time
    # index 7 = max_pixel_dec_time
    # index 8 = integrated_flux
    # index 9 = integrated_flux_error
    # index 10 = snr
    # index 11 = max_pixel_flux
    # index 12 = image_rms

    for island in fluxes:
        # better 359.3... than -0.6...
        if weighted_positions[island][0] < 0.0:
            weighted_positions[island][0] += 360.0
        if weighted_positions[island][2] < 0.0:
            weighted_positions[island][2] += 360.0
        print >> text_file, island, ',', "%.6f" % weighted_positions[island][0], ',', "%.6f" % abs(weighted_positions[island][1]), ',', weighted_positions[island][4], ',', abs(weighted_positions[island][5]), ',', "%.6f" % max_pixel_positions[island][0], ',', "%.6f" % max_pixel_positions[island][1], ',', max_pixel_positions[island][2], ',', max_pixel_positions[island][3], ',', fluxes[island], ',', flux_errors[island], ',', snr_sources[island], ',', island_max[island], ',', image_rms_dic[island]

    text_file.close()
    print "\nCreated text file with necessary information..."
    print "Saved as... %s" % textfile_name
    return 0


# Function to convert seconds to hh:mm:ss.ss format, returns a string
def time2hms(seconds):
    h=int(seconds/3600)
    m=int(seconds % 3600)/60
    s=seconds-(h*3600)-(m*60)
    h=`h`
    m=`m`
    s="%4.2f" % s
    hms=h.zfill(2)+":"+m.zfill(2)+":"+s.zfill(4)
    return hms


# Find max pixel position to set the clean box around...
def resize_image_array2(name,klass,disk,seq):
    image = WAIPSImage(name,klass,disk,seq)
    xsize = image.header.naxis[0]
    ysize = image.header.naxis[1]

    imageArray = np.array(image.pixels)
    imageArray = imageArray[0,0,0,0,0,:,:]
    imageArray[imageArray==3140.89282227] = 'NaN'

    return imageArray


# get max position (x,y)
def get_position(array):

    max_value = numpy.amax(array)

    got_position = 0
    for x in xrange(array.shape[1]):
        for y in xrange(array.shape[0]):
            if array[x,y] == max_value:
                max_position = [x, y]
                got_position = 1
                break

        if got_position == 1:
            break
    return max_position, max_value


def imean(name, klass, disk, seq, value='std', blc=[0,0], trc=[0,0]):
    imean = AIPSTask('IMEAN')
    imean.inname = name
    imean.inclass = klass
    imean.indisk = disk
    imean.inseq = seq

    imean.dohist = -1
    imean.msgkill = 132

    imean.blc = AIPSList(blc)
    imean.trc = AIPSList(trc)

    imean.pixstd = 0    # = 0 do 2 passes to get one
    imean.doinvers = -1    # < 0 do histogram inside blc/trc
    imean.docat = 1    # put true rms noise in header
    #imean.inp()
    imean.go()

    if value == 'std':
        rms_value = imean.pixstd
    else:
        rms_value = imean.pixavg
    #rms_list.append(rms_value)

    return rms_value


# jmfit for point sources:
def jmfit(filename, fileclass, filedisk, fileseq, blc, trc, max_value, gpos, path2folder):
    jmfit = AIPSTask('JMFIT')

    jmfit.inname = filename
    jmfit.inclass = fileclass
    jmfit.inseq = fileseq
    jmfit.indisk = filedisk

    # this has to be small enough or jmfit pulls a wobbily if too many pixels are included.
    jmfit.blc[1:] = blc
    jmfit.trc[1:] = trc

    jmfit.outname = 'RESID'
    jmfit.outclass = 'JMFIT'

    jmfit.ngauss = 1
    jmfit.ctype[1:] = [0]
    jmfit.gpos[1:] = [gpos]

    jmfit.gmax[1:] = [max_value]
    #jmfit.domax[1:] = [1]
    #jmfit.dopos[1:] = [[None, 1, 1]]
    #jmfit.dowidth[1:] = [[None, 1, 1, 1]]

    jmfit.fwidth[1][1] = 0
    jmfit.fwidth[1][2] = 0
    jmfit.fwidth[1][3] = 0
    jmfit.domax[1:] = [1]
    jmfit.dopos[1][1] = 1
    jmfit.dopos[1][2] = 1
    jmfit.dowidth[1][1] = 1
    jmfit.dowidth[1][2] = 1
    jmfit.dowidth[1][3] = 1

    os.environ['MYAREA'] = path2folder

    jmfit.doprint = -3
    
    #jmfit.fitout = path2folder + 'jmfit.txt'
    jmfit.fitout = 'MYAREA:jmfit.txt'

    jmfit.niter = 4000

    jmfit.input()
    jmfit.go()


# jmfit reader... from text file output to get fluxes, positions and errors
def jmfit_reader(order, path2folder, fluxes, flux_errors):
    jmfit_file = open(path2folder + 'jmfit.txt', 'r')
    peak_count = 0
    int_count = 0
    ra_count = 0
    dec_count = 0
    ra_positions = {}
    dec_positions = {}
    for line in jmfit_file:
        if 'Peak intensity' in line:
            line = line.rstrip('\n')
            line = line.rsplit('=')
            line = line[1].rsplit('+/-')
            peak_flux = line[0].strip(' ')
            line = line[1].rstrip(' JY/BEAM')
            peak_error = line.strip(' ')
            #fluxes[order[peak_count]] = float(peak_flux)
            #flux_errors[order[peak_count]] = float(peak_error)
            #peak_count += 1
        if 'Integral intensity' in line:
            line = line.rstrip('\n')
            line = line.rsplit('=')
            line = line[1].rsplit('+/-')
            int_flux = line[0].strip(' ')
            line = line[1].rstrip(' JANSKYS')
            int_error = line.strip(' ')
            fluxes[order[int_count]] = float(int_flux)
            flux_errors[order[int_count]] = float(int_error)
            int_count += 1
        if 'RA' in line and '+/-' in line:
            line = line.rstrip('\n')
            line = line.rsplit('+/-')
            ra_error = line[1].strip(' ')
            ra = line[0].rsplit('RA')[1][1:]
            for digit in xrange(len(ra)+1):
                if ra[digit] == ' ' and ra[digit-1] == ' ':
                    ra = ra[:(digit-1)]
                    break
            ra_degrees = ra2degrees(ra)
            ra_error_degrees = float(ra_error)/3600.0
            ra_positions[order[ra_count]] = [ra_degrees, ra_error_degrees, ra, ra_error]
            ra_count += 1
        if 'DEC' in line and '+/-' in line:
            line = line.rstrip('\n')
            line = line.rsplit('+/-')
            dec_error = line[1].strip(' ')
            dec = line[0].rsplit('DEC')[1][1:]
            for digit in xrange(len(dec)+1):
                if dec[digit] == ' ' and dec[digit-1] == ' ':
                    dec = dec[:(digit-1)]
                    break
            dec_degrees = dec2degrees(dec)
            dec_error_degrees = float(dec_error)/3600.0
            dec_positions[order[dec_count]] = [dec_degrees, dec_error_degrees, dec, dec_error]
            dec_count += 1

    return fluxes, flux_errors, ra_positions, dec_positions


def rms(array):
    rms = ((array**2).mean())**0.5
    #rms = numpy.median(array**2)**0.5
    return rms

def rms2(array):
    #rms = ((array**2).mean())**0.5
    rms = (numpy.mean(array**2))**0.5
    rms2 = numpy.median(array**2)**0.5
    return rms, rms2

# coordinates in degrees to time
def degrees2time(ra, dec):

    if ra < 0:
        ra = ra + 360.0

    ra_h = int(ra/15)
    ra_m = int((ra-15*ra_h)*4)
    ra_s = (4*ra-60*ra_h-ra_m)*60
    ra_h=`ra_h`
    ra_m=`ra_m`
    ra_s="%4.5f" % ra_s
    ra_degrees = ra_h.zfill(2) + " " + ra_m.zfill(2) + " " + ra_s.zfill(6)

    dec *= 3600
    dec_h = int(dec/ 3600)
    dec_m = int(abs(dec) % 3600)/60
    dec_s = abs(dec) - (abs(dec_h)*3600) - (abs(dec_m)*60)
    dec_h=`dec_h`
    dec_m=`dec_m`
    dec_s="%4.4f" % dec_s
    dec_degrees = dec_h.zfill(2) + " " + dec_m.zfill(2) + " " + dec_s.zfill(6)

    return ra_degrees, dec_degrees

def degrees2time2(ra, dec):

    if ra < 0:
        ra = ra + 360.0

    ra_h = int(ra/15)
    ra_m = int((ra-15*ra_h)*4)
    ra_s = (4*ra-60*ra_h-ra_m)*60
    ra_h=`ra_h`
    ra_m=`ra_m`
    ra_s="%.2f" % ra_s
    ra_degrees = ra_h.zfill(2) + " " + ra_m.zfill(2) + " " + ra_s

    dec *= 3600
    dec_h = int(dec/ 3600)
    dec_m = int(dec % 3600)/60
    dec_s = dec - (dec_h*3600) - (dec_m*60)
    dec_h=`dec_h`
    dec_m=`dec_m`
    dec_s="%.2f" % dec_s
    dec_degrees = dec_h.zfill(2) + " " + dec_m.zfill(2) + " " + dec_s
    #print ra_degrees, dec_degrees
    return ra_degrees, dec_degrees


# converts time to degrees... needs a space between hours, minutes, seconds...
def ra2degrees(ra):
    pointing_ra = ra.rsplit(" ")

    if len(pointing_ra) == 3:
        position_ra_degrees = 15*(float(pointing_ra[0]) + (float(pointing_ra[1])/60.0) + (float(pointing_ra[2])/3600.0))

    return position_ra_degrees

# converts time to degrees... needs a space between hours, minutes, seconds...
def dec2degrees(dec):
    pointing_dec = dec.rsplit(" ")

    if len(pointing_dec) == 3:
        position_dec_degrees = (float(pointing_dec[0]) + (float(pointing_dec[1])/60.0) + (float(pointing_dec[2])/3600.0))

    return position_dec_degrees

# Find weighted position of each island but efficiently - only cycling throught entire image array once!
def weighted_mean_coordinates(island_peaks, island_array, array, fluxes_with_noise):

    island_coordinates = collections.OrderedDict()
    weightedpixels = collections.OrderedDict()

    for name in island_peaks.keys():
        weightedpixels[name] = [0,0,0,0] # set up a dictionary, key = each island, value = a list of [weighted x, weighted y, error x, error y]

    for y in xrange(island_array.shape[0]):
        for x in xrange(island_array.shape[1]):

            if island_array[y,x] == 0:
                continue
            else:
                island = 'Island '+str(int(island_array[y,x]))

                weightedpixels[island][0] += (array[y,x]*x/fluxes_with_noise[island]) # weighted x
                weightedpixels[island][1] += (array[y,x]*y/fluxes_with_noise[island]) # weighted y
                weightedpixels[island][2] += (array[y,x]/fluxes_with_noise[island])**2 # error x
                weightedpixels[island][3] += (array[y,x]/fluxes_with_noise[island])**2 # error y

    for island in weightedpixels.keys():
        error_x = math.sqrt(weightedpixels[island][2])
        error_y = math.sqrt(weightedpixels[island][3])

        errors = errors_on_weighted_mean(error_y, error_x, image)
        coord = xyval(weightedpixels[island][1], weightedpixels[island][0], image)

        island_coordinates[island] = [coord[0], coord[1], coord[2], coord[3], errors[0], errors[1]]

    return island_coordinates


# Find position of islands with fluxes as weights in the weighted mean.
def weighted_mean_coordinates_old(island_peaks, island_array, array, fluxes_with_noise):

    island_coordinates = collections.OrderedDict()
    
    # position from weighted mean of fluxes
    for peaks in island_peaks:

        island_num = float(peaks.split(' ')[1])
        number_of_pixels = count[peaks]

        flux_with_noise = fluxes_with_noise[peaks]
 
        weighted_x = 0
        weighted_y = 0

        error_x = 0
        error_y = 0

        for y in xrange(island_array.shape[0]):
            for x in xrange(island_array.shape[1]):
                if island_array[y,x] == island_num:

                    weighted_y += (array[y,x]*y/flux_with_noise)
                    weighted_x += (array[y,x]*x/flux_with_noise)
                    error_y += (array[y,x]/flux_with_noise)**2
                    error_x += (array[y,x]/flux_with_noise)**2
        
        error_x = math.sqrt(error_x)
        error_y = math.sqrt(error_y)

        coord = xyval(weighted_y, weighted_x, image)

        errors = errors_on_weighted_mean(error_y, error_x, image)

        island_coordinates[peaks] = [coord[0], coord[1], coord[2], coord[3], errors[0], errors[1]]

    return island_coordinates


# errors on weighted mean from pixel to degrees
def errors_on_weighted_mean(error_y, error_x, image):

    # value of each pixel
    ra_pixel_increment = image.header.cdelt[0]    # both in degrees
    dec_pixel_increment = image.header.cdelt[1]

    dec_error = error_y*dec_pixel_increment
    ra_error = error_x*ra_pixel_increment

    source_position = degrees2time(ra_error, dec_error)

    return ra_error, dec_error



def local_background(island_array, island_peaks, island_pixels, count, rms_arcsecond_radius, image):

    island_background = {}
    #background = numpy.zeros([island_array.shape[0], island_array.shape[1]], dtype=float)

    pixinc = 3600*(image.header.cdelt[1])
    rms_pixel_radius = round(rms_arcsecond_radius/pixinc,0)
    num_pix_inbox = (rms_pixel_radius*2)**2
    
    for islandname in island_peaks:

        island_background[islandname] = []
        island_num = float(islandname.split(' ')[1])
        
        ymin = island_peaks[islandname][0]-rms_pixel_radius
        ymax = island_peaks[islandname][0]+rms_pixel_radius
        xmin = island_peaks[islandname][1]-rms_pixel_radius
        xmax = island_peaks[islandname][1]+rms_pixel_radius

        if ymin < 1:
            ymin == 2
        if ymax > island_array.shape[0]:
            ymax == island_array.shape[0]-1
        if xmin < 1:
            xmin == 2
        if xmax > island_array.shape[1]:
            xmax == island_array.shape[1]-1
        
        counter = 0
        for y in xrange(1,island_array.shape[0]):
            for x in xrange(1,island_array.shape[1]):

                if (y < ymax and y >= ymin and x < xmax and x >= xmin):
                    if island_array[y][x] != island_num:
                        #background[y][x] = island_num
                        island_background[islandname].append([y, x])
                        counter += 1

        
    return island_background



def floodfill(seed_threshold, flood_threshold, array, beam_size, noisearray, previous_run_pixels=[]):
    # list with island pixel positions. Need dictionary for multiple islands.
    island_pixels = collections.OrderedDict()
    #print array, len(array[0]), len(array)
    # array the same size as the image. Each island has a number...
    island_array = numpy.zeros([array.shape[0], array.shape[1]], dtype=float)

    # island counter... needed for dictionary.
    island_number = 1

    pixels_before = 0
    # Passage for finding the seeds for the different islands
    count = collections.OrderedDict()
    island_peaks = collections.OrderedDict()
    island_max = collections.OrderedDict()

    seed_pixels = []
    if len(noisearray) > 0:
        for y in xrange(array.shape[0]):
            for x in xrange(array.shape[1]):
                if array[y,x] > noisearray[y,x]:
                    tmp = [y, x, noisearray[y,x]]
                    seed_pixels.append(tmp)

    else:
        for y in xrange(array.shape[0]):
            for x in xrange(array.shape[1]):
                if array[y,x] > seed_threshold:
                    #seed_pixels.append([y,x])
                    tmp = [y, x, rms_image*sigma_S]
                    seed_pixels.append(tmp)
                    
    for seed in seed_pixels:
        y = seed[0]
        x = seed[1]
        flood_threshold = (seed[2]/sigma_S)*sigma_F
    
        if island_array[y, x] == 0.0:  # so not to test the same island twice...
            
            islandname = 'Island '+str(island_number)
            tmpislandpix = []

            island_pixels[islandname] = flood_island(array, tmpislandpix, y, x, flood_threshold, beam_size)

            if len(island_pixels[islandname]) > ((beam_size - 1)*beampercentage):
                print "Land Ahoy!"
                print "Growing Island number: %i" % (island_number)
                
                count[islandname] = len(island_pixels[islandname])
                #pixels_before = len(island_pixels)

                # update island_array with island pixels for island number
                max_position = []
                max_value = 0
                for pixel in island_pixels[islandname]:
                    if island_array[pixel[0], pixel[1]] == 0.0:
                        if array[pixel[0], pixel[1]] > max_value:
                            max_value = array[pixel[0], pixel[1]]
                            max_position = [pixel[0], pixel[1]]
                        island_array[pixel[0], pixel[1]] = island_number
                island_peaks[islandname] = max_position
                island_max[islandname] = max_value
                island_number += 1    # identifier for next island
            
            else:
                print "False alarm... Spurious pixel!"
                del island_pixels[islandname]

    return island_array, count, island_peaks, island_max, island_pixels


# definition to test pixels adjacent to a `hot' pixel or pixel in an island.
def test_adjacent_pixels(array, y, x, island_pixels, flood_threshold):
    # Definition to test adjacent pixels to pixel already confirmed as being part of the island.

    new_island_pixels = []
    adjacent_pixels = []
    adjacent_pixels.append([y, x+1])
    adjacent_pixels.append([y, x-1])
    adjacent_pixels.append([y+1, x])
    adjacent_pixels.append([y-1, x])


    # checking for edge pixels, and removing if true.
    for pixel in adjacent_pixels:
        if pixel[0] == 0 or pixel[0] == 1 or pixel[0] == array.shape[0] or pixel[0] == array.shape[0]-1:
            adjacent_pixels.remove(pixel)
        elif pixel[1] == 0 or pixel[1] == 1 or pixel[1] == array.shape[1] or pixel[1] == array.shape[1]-1:
            adjacent_pixels.remove(pixel)

    for pixel in adjacent_pixels:
        if pixel not in island_pixels and array[pixel[0], pixel[1]] > flood_threshold:
            #print "aaa", pixel
            new_island_pixels.append(pixel)

    return new_island_pixels


# once a seed pixel has been found, grow the island.
def flood_island(array, island_pixels, y, x, flood_threshold, beam_size):

    # Found land from the seed threshold... Now grow island by repeatedly finding adjacent pixels with values > flood threshold level

    beginning = len(island_pixels)
    before = len(island_pixels)
    island_pixels.append([y,x])
    after = len(island_pixels)
    to_add = []

    cycles = []
    while after > before:
        before = after
        for pixel in xrange(len(island_pixels[:beginning]), len(island_pixels)):
            y = island_pixels[pixel][0]
            x = island_pixels[pixel][1]
            new = test_adjacent_pixels(array, y, x, island_pixels, flood_threshold)
            if len(new) > 0:
                for p in new:
                    to_add.append(p)
        for p in to_add:
            if p not in island_pixels:
                island_pixels.append(p)
        after = len(island_pixels)
        diff = after - before
        cycles.append(diff)
        #if after > beam_size*1.2:    # put in as SNR=100 gets stuck sometimes...
        if len(cycles) > 3:
            #if cycles[-1] < 0.1*beam_size: # or % of beam size < 0.1*beam_size
                #break
            #if len(cycles) > 200:
            if len(cycles) > 300:
                print "Too many cycles... breaking out"
                break

    return island_pixels


def plot_island(island_array, array, name, peak, image, pix_count, pixel_position, flux, flux_error):

    import matplotlib.pyplot as plt
    import matplotlib.cm as cm

    outname = 'Island'+name.split(' ')[1]
    
    peak.reverse()

    plot_radius_arcs = 2.
    pixinc = 3600*(image.header.cdelt[1])
    plot_radius_pix = round(plot_radius_arcs/pixinc,0)
    num_pix_inbox = (plot_radius_pix*2)**2
    pic_array_diam = plot_radius_pix*2

    ymin = peak[0]-plot_radius_pix
    ymax = peak[0]+plot_radius_pix
    xmin = peak[1]-plot_radius_pix
    xmax = peak[1]+plot_radius_pix

    if ymin < 0:
        ymin = 0
        ymax = pic_array_diam
    if ymax > len(island_array[0]):
        ymax = len(island_array[0])
        ymin = len(island_array[0])-pic_array_diam
    if xmin < 0:
        xmin = 0
        xmax = pic_array_diam
    if xmax > len(island_array[1]):
        xmax = len(island_array[1])
        xmin = len(island_array[1])-pic_array_diam

    plot_array = island_array[ymin:ymax,xmin:xmax]
    pic_array = array[ymin:ymax,xmin:xmax]*10**6
    
    fig, (ax1, ax2) = plt.subplots(1,2)

    fig.suptitle(filename+' .'+fileclass+'. '+str(fileseq)+'. '+str(filedisk), fontsize=15)

    ax1.imshow(plot_array, origin='lower', cmap="hot")
    picimg = ax2.imshow(pic_array, origin='lower', cmap="jet")

    cax = fig.add_axes([0.91,0.265,0.015,0.47])
    cbar = fig.colorbar(picimg, cax=cax)

    ax1.set_title('Detected Area = %i Pixels' % pix_count)
    ax2.set_title('%s' % outname)

    ax2.get_yaxis().set_visible(False)

    raticklist = []
    decticklist = []
    pixra_ticklist = []
    pixdec_ticklist = []
    rastrlist = []
    decstrlist = []

    numofticks = 4
    count = 0
    for x in xrange(int(xmin), int(xmax), pic_array.shape[1]/numofticks):
        raticklist.append(x)
        pixra_ticklist.append(count)
        count += (pic_array.shape[1]/numofticks)
    count = 0
    for y in xrange(int(ymin), int(ymax), pic_array.shape[0]/numofticks):
        decticklist.append(y)
        pixdec_ticklist.append(count)
        count += (pic_array.shape[1]/numofticks)  

    raticklist.append(xmax)
    decticklist.append(ymax)
    pixra_ticklist.append(pic_array.shape[1]-1)
    pixdec_ticklist.append(pic_array.shape[0]-1)

    for tick in xrange(len(raticklist)):
        ra, dec = getaxescoords(decticklist[tick], raticklist[tick], image, units='hms')
        rastrlist.append(ra)
        decstrlist.append(dec)

    ax1.set_xticks(pixra_ticklist)
    ax1.set_xticklabels(rastrlist, fontsize=6)
    ax1.set_xlabel('RA (J2000)', fontsize=8)
    ax1.set_yticks(pixdec_ticklist)
    ax1.set_yticklabels(decstrlist, fontsize=6)
    ax1.set_ylabel('DEC (J2000)', fontsize=8)
    ax2.set_xticks(pixra_ticklist)
    ax2.set_xticklabels(rastrlist, fontsize=6)
    ax2.set_xlabel('RA (J2000)', fontsize=8)
    ax2.set_yticks(pixdec_ticklist)
    ax2.set_yticklabels(decstrlist, fontsize=6)

    statement1 = "Integrated Flux: %.1f +/- %.1f $\mu$Jy" % ((flux*10**6),(flux_error*10**6))
    statement2 = "Beam Size = %.1f pixels" % beam_size
    statement3 = "Maximum = %.1f $\mu$Jy at pixel(x,y) %i, %i" % ((array[peak[0],peak[1]]*10**6), peak[1]+1,peak[0]+1)
    statement4 = "Sky Pos RA: %s  DEC: %s " % (pixel_position[2],pixel_position[3])
    statement5 = "$\sigma_{s}$ = %.1f \n $\sigma_{f}$ = %.1f" % (sigma_S, sigma_F)

    fig.text(0.5, 0.18,statement1,horizontalalignment='center')
    fig.text(0.5,0.14,statement2,horizontalalignment='center')
    fig.text(0.5, 0.10,statement3,horizontalalignment='center')
    fig.text(0.5, 0.06,statement4,horizontalalignment='center')
    fig.text(0.5, 0.85,statement5,horizontalalignment='center')

    figname = outname+'.png'
    fig.savefig(workingdir+figname)
    #print "\n Saved image and detected area to %s" % workingdir+outname+'.png'
    return str(workingdir)+str(figname)

def getnoisemap(array, image, sigma_S, noisemapres, plottedarraynames, rms_image):

    y_dim = array.shape[0]
    x_dim = array.shape[1]

    rmsboxsize = y_dim/noisemapres # this chooses the rough pixel size for each segament, the function will calculate the a preferred number in order to yeild the most unifrom spread of noise estimates across the image
    
    y_num = y_dim/rmsboxsize
    x_num = x_dim/rmsboxsize
    numofnoisemeasurements = y_num*x_num

    noisearray = np.zeros([y_dim, x_dim], dtype=float)

    bltrc_dic = {}
    counter = 1
    for y in xrange(y_num):
        for x in xrange(x_num):

            y0 = y*rmsboxsize
            x0 = x*rmsboxsize
            y1 = (y*rmsboxsize)+rmsboxsize
            x1 = (x*rmsboxsize)+rmsboxsize

            if y == (y_num-1):
                y1 = y_dim
            if x == (x_num-1):
                x1 = x_dim

            bltrc_dic[counter] = [x0,y0,x1,y1]
            counter += 1

    noise_dic = {}
    print "\nAbout to run imean %i times...it shouldn't be too long..." % numofnoisemeasurements
    for key, bltrc in bltrc_dic.items():
        x0 = bltrc[0]
        x1 = bltrc[2]
        y0 = bltrc[1]
        y1 = bltrc[3]

        blc = [x0,y0]
        trc = [x1,y1]

        try:
            noise = round(imean(filename, fileclass, filedisk, fileseq, value = 'std', blc=blc, trc = trc), 7)
            noisearray[y0:y1,x0:x1] = noise*sigma_S
        except:
            noise = 0        
            noisearray[y0:y1,x0:x1] = 'NaN'


    # Section to plot the noise map and save the figure!
    fig = plt.figure()
    a=fig.add_subplot(1,1,1)

    noiseplot = 10**6*noisearray

    imgplot = plt.imshow(noiseplot, origin='lower')
    
    a.set_title('%.1f$\sigma$ Noise Map' % sigma_S)
    cax = fig.add_axes([0.85,0.1,0.02,0.8])
    cbar = fig.colorbar(imgplot, cax=cax)
    statement1 = 'Resolution = %i image pixels' % rmsboxsize
    fig.text(0.5,0.015, statement1,horizontalalignment='center')

    statement1 = "Colour Bar Units: $\mu$Jy"
    fig.text(0.95,0.5, statement1, rotation=90, verticalalignment='center')

    raticklist = []
    decticklist = []
    rastrlist = []
    decstrlist = []

    numofticks = 4
    for x in xrange(0, noiseplot.shape[1], (noiseplot.shape[1]/numofticks)):
        raticklist.append(x)
    for y in xrange(0, noiseplot.shape[0], (noiseplot.shape[0]/numofticks)):
        decticklist.append(y)            

    raticklist.append(noiseplot.shape[1]-1)
    decticklist.append(noiseplot.shape[0]-1)

    for tick in xrange(len(raticklist)):
        ra, dec = getaxescoords(decticklist[tick], raticklist[tick], image, units='hms')
        rastrlist.append(ra)
        decstrlist.append(dec)

    a.set_xticks(raticklist)
    a.set_xticklabels(rastrlist, fontsize=8)
    a.set_xlabel('RA (J2000)', fontsize=10)
    a.set_yticks(decticklist)
    a.set_yticklabels(decstrlist, fontsize=8)
    a.set_ylabel('DEC (J2000)', fontsize=10)

 
    fig.savefig(workingdir+filename+'_NM.png')
    print "\n Saved image and detected area to %s" % workingdir+filename+'_NM.png'
    plottedarraynames['Noise_Map'] = workingdir+filename+'_NM.png'

    return noisearray


def mergepngs(filename, woringdir, namedict):

    mergedfile = filename+'.pdf'

    string = ''
    for value in namedict.values():
        string += str(value)+' '
    
    os.system('/usr/bin/convert '+str(string)+str(workingdir)+'/'+str(mergedfile))

    print "\nMerged all .png files into one pdf file as \n-->%s" % str(workingdir)+'/'+str(mergedfile)

    os.system('rm '+str(workingdir)+'/*.png')



def xyval(y, x, image):

    # First convert the x,y python array pixel to the same pixel in AIPS speak (fortran starts at 1, python at 0)
    xpix = x+1
    ypix = y+1

    # CRPIX in the image header is the reference pixel location (i.e. of the centre of the image wrt the coordinate centre in the header)
    rploc_x = image.header['crpix'][0]
    rploc_y = image.header['crpix'][1]
    # CDELT in the image header is the x and y increments, i.e. the length of 1 pixel in degrees
    xinc = image.header['cdelt'][0]
    yinc = image.header['cdelt'][1]
    # RPVAL in the image header is the coords in degrees of the coordinate centre
    rpval_x = image.header['crval'][0]
    rpval_y = image.header['crval'][1]

    # Find the difference between our desired pixel and the reference pixel in units radians
    dx = (xpix-rploc_x)*xinc*(math.pi/180)
    dy = (ypix-rploc_y)*yinc*(math.pi/180)

    # Now change the definition of these things to match as they are in the NEWPOS function of AIPS
    L = dx
    M = dy 
    RA0 = rpval_x * (math.pi/180.)
    DEC0 = rpval_y * (math.pi/180.)

    # Now do the maths as is done in AIPS function NEWPOS
    SINS = L*L + M*M
    COS0 = math.cos(DEC0)
    SIN0 = math.sin(DEC0)
    COSS = math.sqrt(1.-SINS)
    DT = SIN0 * COSS + COS0 * M
    DECT = math.asin(DT)
    RAT = COS0 * COSS - SIN0 * M
    RAT = math.atan2(L, RAT) + RA0

    # Convert RAT, DECT from radians to degrees
    radegrees = RAT/(math.pi/180)
    decdegrees = DECT/(math.pi/180)

    source_position = degrees2time(radegrees, decdegrees)

    return radegrees, decdegrees, source_position[0], source_position[1]



def getaxescoords(y, x, image, units='hms'):

    # First convert the x,y python array pixel to the same pixel in AIPS speak (fortran starts at 1, python at 0)
    xpix = x+1
    ypix = y+1

    # CRPIX in the image header is the reference pixel location (i.e. of the centre of the image wrt the coordinate centre in the header)
    rploc_x = image.header['crpix'][0]
    rploc_y = image.header['crpix'][1]
    # CDELT in the image header is the x and y increments, i.e. the length of 1 pixel in degrees
    xinc = image.header['cdelt'][0]
    yinc = image.header['cdelt'][1]
    # RPVAL in the image header is the coords in degrees of the coordinate centre
    rpval_x = image.header['crval'][0]
    rpval_y = image.header['crval'][1]

    # Find the difference between our desired pixel and the reference pixel in units radians
    dx = (xpix-rploc_x)*xinc*(math.pi/180)
    dy = (ypix-rploc_y)*yinc*(math.pi/180)

    # Now change the definition of these things to match as they are in the NEWPOS function of AIPS
    L = dx
    M = dy 
    RA0 = rpval_x * (math.pi/180.)
    DEC0 = rpval_y * (math.pi/180.)

    # Now do the maths as is done in AIPS function NEWPOS
    SINS = L*L + M*M
    COS0 = math.cos(DEC0)
    SIN0 = math.sin(DEC0)
    COSS = math.sqrt(1.-SINS)
    DT = SIN0 * COSS + COS0 * M
    DECT = math.asin(DT)
    RAT = COS0 * COSS - SIN0 * M
    RAT = math.atan2(L, RAT) + RA0

    # Convert RAT, DECT from radians to degrees
    radegrees = RAT/(math.pi/180)
    decdegrees = DECT/(math.pi/180)

    if units == 'deg':
        return round(radegrees,5), round(decdegrees,5)
    if units == 'hms':
        rastr, decstr = degrees2time2(radegrees, decdegrees)
        return rastr, decstr


################################################################################################
################################################################################################
################################################################################################
### MAIN CODE ##################################################################################


if __name__ == '__main__':

    #AIPSTask.msgkill = 132 # this will supress AIPS from 'chatting shit' - set to a negative number to suppress but log the 'shit chat'

    #First let's create a directory within the path2folder with the image name as the directory name...
    workingdir = path2folder+outname+'_SEAC/'
    try:
        os.mkdir(workingdir)
    except OSError:
        print '\nFolder already exists...shall I delete its contents...?'
        delete = raw_input("\nType 'y' to delete, 'n' to continue or 'e' for exit: ")
        if delete == 'y':
            os.system('rm -r '+workingdir+'/*')
        if delete == 'e':
            sys.exit(0)
        if delete == 'n':
            print 'Onwards!'

    # Read in the array from AIPS image file.
    array = resize_image_array2(filename, fileclass, filedisk, fileseq)
    
    image = AIPSImage(filename, fileclass, filedisk, fileseq)

    plottedarraynames = collections.OrderedDict()

    # Get intial RMS of image using IMEAN
    rms_image = imean(filename, fileclass, filedisk, fileseq)
    print "\nInitial RMS of image: %f" % (rms_image)
    
    # Read in the image and estimate beam size from Image Header
    image = AIPSImage(filename, fileclass, filedisk, fileseq)
    
    beam_area = image.header.bmaj*image.header.bmin*math.pi/(4*math.log(2))
    pixel_area = abs(image.header.cdelt[0]*image.header.cdelt[1])
    beam_size = beam_area/pixel_area
    print "Beam size has %f pixels." % (beam_size)
    
    # Section to get calculate the noise variance across the image!    
    if usenoisemap == 'yes':
        tnoisemap = time.time()
        noisearray = getnoisemap(array, image, sigma_S, noisemapres, plottedarraynames, rms_image)
        print "\nTime Taken to create noise map: ", time2hms(time.time()-tnoisemap)
    else:
        noisearray = []

    # initialise the thresholds
    if faint_detection == 'no':
        seed_threshold = sigma_S*rms_image 
        flood_threshold = sigma_F*rms_image
    else:
        seed_threshold = 4.0*rms_image
        flood_threshold = 2.56*rms_image

    
    print "\nFirst run of Floodfill algorithm..."

    tfloodfill = time.time()
    results = floodfill(seed_threshold, flood_threshold, array, beam_size, noisearray)
    print "\nTime Taken to complete Floodfill Algorithm: ", time2hms(time.time()-tfloodfill)
    
    island_array = results[0]
    count = results[1]
    island_peaks = results[2]
    island_max = results[3]
    island_pixels = results[4]

 
    # update the copied image with island array:
    if create_mask_of_detection == 'yes':
        image = WAIPSImage(filename, maskclass, maskdisk, maskseq)
        image.pixels[:] = island_array[:]
        image.update()


    ##################################################################
    ##################################################################
    ##################################################################
    ### JMFIT SECTION - obtain fluxes using AIPS' jmfit function
    ##################################################################

    if fluxes_from_jmfit == 'yes':
        if os.path.exists(workingdir + 'jmfit.txt') == True:
            os.remove(workingdir + 'jmfit.txt')
        order = []
        fluxes = {}
        flux_errors = {}
        local_rms_dic = {}
        if len(island_peaks) > 0:
            for peaks in island_peaks:
                order.append(peaks)
                max_position = island_peaks[peaks]
                max_value = island_max[peaks]
                max_value = math.ceil(max_value * (10**4)) / (10**4)

                # get clean box corners around max pixel position
                blcy = max_position[0] - int(0.01*island_array.shape[0])
                blcx = max_position[1] - int(0.01*island_array.shape[1])
                trcy = max_position[0] + int(0.01*island_array.shape[0])
                trcx = max_position[1] + int(0.01*island_array.shape[1])

                # make sure search box stays within image
                if blcx < 0:
                    blcx = 0
                if blcy < 0:
                    blcy = 0

                if trcx > island_array.shape[1]-1:
                    trcx = island_array.shape[1]-1
                if trcy > island_array.shape[0]-1:
                    trcy = island_array.shape[0]-1

                blc = [blcx, blcy]
                trc = [trcx, trcy]

                gpos = [None, max_position[1]+1, max_position[0]+1]

                jmfit(filename, fileclass, filedisk, fileseq, blc, trc, max_value, gpos, workingdir)

            jmfit_output = jmfit_reader(order, workingdir, fluxes, flux_errors)

            fluxes = fluxes
            flux_errors = flux_errors

            weighted_positions = collections.OrderedDict()
            for island in jmfit_output[2]:
                for source in jmfit_output[3]:
                    if island == source:
                        weighted_positions[island] = [jmfit_output[2][island][0], jmfit_output[3][island][0], jmfit_output[2][island][2], jmfit_output[3][island][2], jmfit_output[2][island][1], jmfit_output[3][island][1]]

            rms_image = imean(filename, fileclass, filedisk, fileseq, 'std')
            for island in island_peaks:
                local_rms_dic[island] = rms_image

    
    ##################################################################
    ##################################################################
    ##################################################################
    ### Get fluxes for each Island using the local background
    ##################################################################

    else:
        if noise_from_local_background == 'yes':
            tb = time.time()
            print "\n\nCreating a local background array to calculate the local RMS of each Island found..."
            background = local_background(island_array, island_peaks, island_pixels, count, rms_arcsecond_radius, image)
            print "Time Taken to Create Local Background Array: ", time2hms(time.time()-tb)

            if create_mask_of_detection == 'yes':
                image = WAIPSImage(filename, maskclass, maskdisk, maskseq)
                image.pixels[:] = background[:]
                image.update()
        
        print "\n Calculating Island fluxes..."
        image = WAIPSImage(filename, fileclass, filedisk, fileseq)
        beam_area = image.header.bmaj*image.header.bmin*math.pi/(4*math.log(2))
        pixel_area = abs(image.header.cdelt[0]*image.header.cdelt[1])
        beam_size = beam_area/pixel_area

        fluxes = collections.OrderedDict()
        fluxes_with_noise = collections.OrderedDict()
        flux_errors = collections.OrderedDict()
        local_rms_dic = collections.OrderedDict()

        for islandname, numpixels in count.items():
            flux_with_noise = 0.
            islandnum = float(islandname.split(' ')[1])

            for pixposition in island_pixels[islandname]:
                flux_with_noise += array[pixposition[0], pixposition[1]]

            fluxes_with_noise[islandname] = flux_with_noise
            flux_with_noise = flux_with_noise/beam_size
            print "\nUncorrected Flux for %s: %f Jy over %i pixels" % (islandname, flux_with_noise, numpixels)

            if noise_from_local_background == 'no': # calculate mean and rms from entire image using IMEAN...
                mean = imean(filename, fileclass, filedisk, fileseq, 'mean')
                rms_image = imean(filename, fileclass, filedisk, fileseq, 'std')

                true_flux = flux_with_noise - (mean*(numpixels/beam_size))
                error = rms_image*(math.sqrt(numpixels/beam_size))        
                fluxes[islandname] = true_flux
                flux_errors[islandname] = error
                local_rms_dic[islandname] = rms_image

            if noise_from_local_background == 'yes': # calculate mean and rms from local background, size depends on your rms_arcsecond_radius
                rms_from_background = []

                for pixposition in background[islandname]:
                    rms_from_background.append(array[pixposition[0],pixposition[1]])

                rms_from_background = numpy.array(rms_from_background)

                rms_image = numpy.std(rms_from_background)
                mean_background = numpy.mean(rms_from_background)

                true_flux = flux_with_noise - (mean_background*(numpixels/beam_size))
                error = rms_image*(math.sqrt(numpixels/beam_size))        
                fluxes[islandname] = true_flux
                flux_errors[islandname] = error
                local_rms_dic[islandname] = rms_image

                
        # Now find the weighted coordinate positions if so desired...this will take a bit longer as it needs to cycle through the entire array again...
        if findweightedcorrds == 'yes':
            weighted_positions = weighted_mean_coordinates(island_peaks, island_array, array, fluxes_with_noise)
        else:
            weighted_positions = {}
            for island in island_peaks:
                weighted_positions[island] = [0.0,0.0,0.0,0.0,0.0,0.0]


    # Find position of max_pixel through parseltongue...
    max_pixel_positions = collections.OrderedDict()
    for island in island_peaks:
        max_pixel_positions[island] = xyval(island_peaks[island][0], island_peaks[island][1], image)


    # Plot the array with the positions of the found islands overplotted...
    
    if plotarray == 'yes':
        
        fig = plt.figure()
        a=fig.add_subplot(1,1,1)
        arrayplot = 10**6*array
        imgplot = plt.imshow(arrayplot, origin='lower',aspect='equal', zorder=1)
        a.set_title('Input Image - %s' % filename)

        statement1 = "Colour Bar Units: $\mu$Jy"
        fig.text(0.95,0.5, statement1, rotation=90, verticalalignment='center')

        plotpeaks = []
        plotpeaksy = []
        plotpeaksx = []
        for value in island_peaks:
            plotpeaks.append(island_peaks[value])
            plotpeaksy.append(island_peaks[value][0])
            plotpeaksx.append(island_peaks[value][1])
        
        plt.xlim([0,arrayplot.shape[1]])
        plt.ylim([0,arrayplot.shape[0]])

        raticklist = []
        decticklist = []
        rastrlist = []
        decstrlist = []

        numofticks = 4
        for x in xrange(0, array.shape[1], (array.shape[1]/numofticks)):
            raticklist.append(x)
        for y in xrange(0, array.shape[0], (array.shape[0]/numofticks)):
            decticklist.append(y)            

        raticklist.append(array.shape[1]-1)
        decticklist.append(array.shape[0]-1)

        for tick in xrange(len(raticklist)):
            ra, dec = getaxescoords(decticklist[tick], raticklist[tick], image, units='hms')
            rastrlist.append(ra)
            decstrlist.append(dec)

        a.set_xticks(raticklist)
        a.set_xticklabels(rastrlist, fontsize=8)
        a.set_xlabel('RA (J2000)', fontsize=10)
        a.set_yticks(decticklist)
        a.set_yticklabels(decstrlist, fontsize=8)
        a.set_ylabel('DEC (J2000)', fontsize=10)

        #count = 0
        for island in island_peaks:
            label = str(island.split(' ')[1])
            xy = island_peaks[island]
            xy.reverse()

            plt.annotate(label, xy, xytext=(-20,20),textcoords = 'offset points', ha = 'right', va = 'bottom', bbox = dict(boxstyle = 'round,pad=0.5', fc = 'white', alpha = 0.5),
            arrowprops = dict(arrowstyle = '->', connectionstyle = 'arc3,rad=0'))

        cax = fig.add_axes([0.85,0.1,0.02,0.8])
        cbar = fig.colorbar(imgplot, cax=cax)

        fig.savefig(workingdir+filename+'_IM.png')

        plottedarraynames[filename] = str(workingdir)+str(filename)+'_IM.png'

        for island, peak in island_peaks.items():
            if findweightedcorrds == 'no':
                plottedarraynames[island] =  plot_island(island_array, array, island, peak, image, count[island], max_pixel_positions[island], fluxes[island], flux_errors[island])
            if findweightedcorrds == 'yes':
                plottedarraynames[island] =  plot_island(island_array, array, island, peak, image, count[island], weighted_positions[island], fluxes[island], flux_errors[island])
                
    # Print Information Nicely:
    snr_sources = collections.OrderedDict()
    for island in fluxes:
        
        print "\n", island
        if findweightedcorrds == 'no':
            print "Coordinates in RA:", max_pixel_positions[island][2], "and DEC:", max_pixel_positions[island][3]
        if findweightedcorrds == 'yes':
            print "Coordinates in RA:", weighted_positions[island][2], "and DEC:", weighted_positions[island][3]
        print "Integrated Flux:", round((fluxes[island]*10**6),1), "microJy, +/-", round((flux_errors[island]*10**6),1), "microJy."
        
        if noise_from_local_background == 'yes' and fluxes_from_jmfit != 'yes':
            print "SNR:", fluxes[island]/ local_rms_dic[island]
            snr_sources[island] = fluxes[island]/ local_rms_dic[island]
        else:
            print "SNR:", fluxes[island]/ local_rms_dic[island]
            snr_sources[island] = fluxes[island]/ local_rms_dic[island]

    if len(island_peaks) > 0:
        if write_2_file == 'yes':
            create_source_list(weighted_positions, max_pixel_positions, fluxes, flux_errors, snr_sources, island_max, local_rms_dic, workingdir, filename, fileclass, fileseq)

    # Run merge function to merge all the plots (.png files) into one .pdf file, then delete the .png files.
    mergepngs(filename, workingdir, plottedarraynames)

    print "\nFlux Extractor script finished."
    print "Time taken (hh:mm:ss):", time2hms(time.time()-ti)
