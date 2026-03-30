#!/usr/bin/env python3
import sys
import zulip
import re
import json

# Usage:
# python scripts/zulip_emoji_reactions.py $ZULIP_API_KEY $ZULIP_EMAIL $ZULIP_SITE $ACTION $NUMBER_OF_COMMENT_TO_SCAN
# The first three variables identify the lean4 Zulip chat and allow the bot to access it
# (see .github/workflows/zulip_emoji_merge_delegate.yaml),
# $NUMBER_OF_COMMENT_TO_SCAN is optional, but if present, it should be the number of past comments in
# `mathlib reviewers` that get inspected.  The default value is 50.

ZULIP_API_KEY = sys.argv[1]
ZULIP_EMAIL = sys.argv[2]
ZULIP_SITE = sys.argv[3]
try:
    PAST_COMMENTS = sys.argv[4]
except:
    PAST_COMMENTS = 50

# The script flags any message that contains one of these emoji reactions
emojis=['butterfly', 'robot']
# The script flags any message that contains one of these substrings, ignoring case
substrings=['zenodo']

print(f"Messages with a reaction in {emojis} or containing {substrings} among the last {PAST_COMMENTS} comments")

# Initialize Zulip client
client = zulip.Client(
    email=ZULIP_EMAIL,
    api_key=ZULIP_API_KEY,
    site=ZULIP_SITE
)

# Fetch the messages from the `mathlib reviewers` channel
reviewers_response = client.get_messages({
    "anchor": "newest",
    "num_before": PAST_COMMENTS,
    "num_after": 0,
    #"narrow": [
    #    {"operator": "channel", "operand": "junk"},
    #],
})

messages=reviewers_response['messages']
#print(len(messages))

for message in messages:
    #if message['sender_full_name'] == 'github mathlib4 bot':
      #print(message)
      content = message['content']
      #id=message['sender_id']
      reactions = message['reactions']
      # Check for emoji reactions
      hasMergeReaction=False
      emojiFound=''
      zenodo=False
      #info=f"thread:  {message['display_recipient']}\nsubject: {message['subject']}"
      info=f"#**{message['display_recipient']}>{message['subject']}** "
      for emo in emojis:
        count=0
        for r in reactions:
          #print(r)
            if r['emoji_name'] == emo:
              hasMergeReaction=True #hasMergeReaction or (r['emoji_name'] == emo) #r['user_id'] == id and
              count+=1
        if count != 0:
          emojiFound=f"{emojiFound}{count} {emo} "
        #print(f"id: {r['user_id']}; emoji: {r['emoji_name']}")
      shouldPrint=emojiFound
      #if hasMergeReaction:
        #continue
        #print(f'\n{info}\nHas robot or butterfly ({emojiFound})')
        #print(content)
      for sub in substrings:
        if re.search(f"{sub}", f"{content}", re.IGNORECASE):
          shouldPrint=True
          zenodo=True
          #print(f"\nContains zenodo:\n{info}")
      if shouldPrint:
        print(f"\n{info}")
        if emojiFound:
          print(f'* {emojiFound.rstrip()}')
        if zenodo:
          print(f"* Contains zenodo")
      #else:
      #  print(content)
        #print('neither merge nor peace_sign reactions found')
      #print('---\n')

'''
Use as follows to get the formatting: it would be good to not have to convert html to md manually,
but I have not looked into an alternative.

./scripts/find_reactions.py API_KEY EMAIL https://leanprover.zulipchat.com |
  sed '
    s=<a href[^#]*==
    s=</a>==
    s=<[/]*strong>=*=g
    s=<[/]*code>=`=g
    s=<[/]*p>==g' |
  sed -z '
    s=<blockquote>\n=> =g
    s=</blockquote>==g'
'''
