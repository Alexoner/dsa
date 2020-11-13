### git
We'll skip basic `git clone/commit/pull/push/commit/revert` usage.
Git commits have a TREE structure!

#### git rebase --onto
Refer to `git help rebase`.

       Assume the following history exists and the current branch is "topic":

                     A---B---C topic
                    /
               D---E---F---G master

       From this point, the result of either of the following commands:

           git rebase master
           git rebase master topic

       would be:

                             A'--B'--C' topic
                            /
               D---E---F---G master

       NOTE: The latter form is just a short-hand of git checkout topic followed by git rebase
       master. When rebase exits topic will remain the checked-out branch.


       Here is how you would transplant a topic branch based on one branch to another, to pretend
       that you forked the topic branch from the latter branch, using rebase --onto.

       First let's assume your topic is based on branch next. For example, a feature developed in
       topic depends on some functionality which is found in next.

               o---o---o---o---o  master
                    \
                     o---o---o---o---o  next
                                      \
                                       o---o---o  topic

       We want to make topic forked from branch master; for example, because the functionality on
       which topic depends was merged into the more stable master branch. We want our tree to look
       like this:

               o---o---o---o---o  master
                   |            \
                   |             o'--o'--o'  topic
                    \
                     o---o---o---o---o  next

       We can get this using the following command:

           git rebase --onto master next topic # transplate range from 'next' to 'topic' onto 'master'


#### git bisect



